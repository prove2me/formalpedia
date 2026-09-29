-- Prove2me | solution 1 for LearnStability.ConvexSCO.theorem3_regularized_erm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T19:38:53.271773+00:00
-- url     : https://prove2.me/submissions/d4729767-1981-416b-9240-be74b83a87ef

import Mathlib
import Definitions.Def_LearnStability_ConvexSCO_Setting
import Definitions.Def_LearnStability_ConvexSCO_Problem

set_option autoImplicit false

namespace P44d4642b

open MeasureTheory LearnStability.ConvexSCO

/-! ### Exchangeability of product measures (coordinate swap) -/

lemma perm_mp {Z : Type*} [MeasurableSpace Z] {ι : Type*} [Fintype ι] (D : Measure Z)
    [SigmaFinite D] (π : Equiv.Perm ι) :
    MeasurePreserving (fun x : ι → Z => fun i => x (π i)) (Measure.pi fun _ => D)
      (Measure.pi fun _ => D) := by
  have hmeas : Measurable (fun x : ι → Z => fun i => x (π i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (π i)
  refine ⟨hmeas, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have : (fun x : ι → Z => fun i => x (π i)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => s (π.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h i
      have := h (π.symm i)
      simpa using this
    · intro h i
      have := h (π i)
      simpa using this
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp π.symm (fun i => D (s i))

lemma swap_mp {Z : Type*} [MeasurableSpace Z] {m : ℕ} (D : Measure Z) [IsProbabilityMeasure D]
    (i : Fin m) :
    MeasurePreserving (fun p : (Fin m → Z) × Z => (Function.update p.1 i p.2, p.1 i))
      ((Measure.pi fun _ : Fin m => D).prod D) ((Measure.pi fun _ : Fin m => D).prod D) := by
  set J := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin m) => Z) with hJdef
  have hJs : MeasurePreserving J.symm ((Measure.pi fun _ : Fin m => D).prod D)
      (Measure.pi fun _ : Option (Fin m) => D) :=
    ⟨J.symm.measurable, Measure.pi_map_piOptionEquivProd (fun _ : Option (Fin m) => D)⟩
  have hJ : MeasurePreserving J (Measure.pi fun _ : Option (Fin m) => D)
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    MeasurePreserving.symm J.symm hJs
  have hσ := perm_mp D (Equiv.swap (none : Option (Fin m)) (some i))
  have hc := hJ.comp (hσ.comp hJs)
  convert hc using 1
  funext p
  obtain ⟨x, rfl⟩ := J.surjective p
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  refine Prod.ext ?_ ?_
  · show Function.update (fun j => x (some j)) i (x none) =
      fun j => x (Equiv.swap none (some i) (some j))
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Equiv.swap_apply_def, hj]
  · show x (some i) = x (Equiv.swap none (some i) none)
    simp

/-! ### Elementary bounds -/

lemma integrable_of_abs_le' {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (c : ℝ) (h : ∀ x, |g x| ≤ c) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable c (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using h x)

section Deterministic

variable {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [MeasurableSpace Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma empRisk_update {f : E → Z → ℝ} {m : ℕ} (S : Fin m → Z) (i : Fin m) (z' : Z) (h : E) :
    empRisk f (Function.update S i z') h = empRisk f S h + (f h z' - f h (S i)) / m := by
  unfold empRisk
  have key : ∑ j, f h (Function.update S i z' j) = ∑ j, f h (S j) + (f h z' - f h (S i)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => f h (S j)) (Finset.mem_univ i)]
    have hs : ∑ j ∈ Finset.univ.erase i, f h (Function.update S i z' j) =
        ∑ j ∈ Finset.univ.erase i, f h (S j) :=
      Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hs, Function.update_self]
    ring
  rw [key]
  ring

lemma empRisk_mid {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) {m : ℕ} (S : Fin m → Z) {h h' : E}
    (hh : h ∈ Hset) (hh' : h' ∈ Hset) :
    empRisk f S ((1 / 2 : ℝ) • h + (1 / 2 : ℝ) • h') ≤
      (empRisk f S h + empRisk f S h') / 2 := by
  unfold empRisk
  have hs : ∑ i, f ((1 / 2 : ℝ) • h + (1 / 2 : ℝ) • h') (S i) ≤
      ∑ i, ((f h (S i) + f h' (S i)) / 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := (hP.convexOn (S i)).2 hh hh' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    linarith
  have hs2 : ∑ i, ((f h (S i) + f h' (S i)) / 2) =
      ((∑ i, f h (S i)) + ∑ i, f h' (S i)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  rw [hs2] at hs
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc (∑ i, f ((1 / 2 : ℝ) • h + (1 / 2 : ℝ) • h') (S i)) / m
      ≤ (((∑ i, f h (S i)) + ∑ i, f h' (S i)) / 2) / m := div_le_div_of_nonneg_right hs hm
    _ = ((∑ i, f h (S i)) / m + (∑ i, f h' (S i)) / m) / 2 := by ring

lemma reg_mid {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) {m : ℕ} (S : Fin m → Z) (lam : ℝ) {h h' : E}
    (hh : h ∈ Hset) (hh' : h' ∈ Hset) :
    regObjective f lam S ((1 / 2 : ℝ) • h + (1 / 2 : ℝ) • h') ≤
      (regObjective f lam S h + regObjective f lam S h') / 2 - lam / 8 * ‖h - h'‖ ^ 2 := by
  unfold regObjective
  have h1 := empRisk_mid hP S hh hh'
  have hn : ‖(1 / 2 : ℝ) • h + (1 / 2 : ℝ) • h'‖ ^ 2 =
      (‖h‖ ^ 2 + ‖h'‖ ^ 2) / 2 - ‖h - h'‖ ^ 2 / 4 := by
    have hpl := parallelogram_law_with_norm ℝ h h'
    have e : (1 / 2 : ℝ) • h + (1 / 2 : ℝ) • h' = (1 / 2 : ℝ) • (h + h') := by rw [smul_add]
    rw [e, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith [hpl]
  rw [hn]
  nlinarith [h1]

lemma reg_gap {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) {m : ℕ} (S : Fin m → Z) (lam : ℝ) {h h' : E}
    (hh : h ∈ Hset) (hh' : h' ∈ Hset)
    (hmin : ∀ g ∈ Hset, regObjective f lam S h ≤ regObjective f lam S g) :
    lam / 4 * ‖h - h'‖ ^ 2 ≤ regObjective f lam S h' - regObjective f lam S h := by
  have hmid := reg_mid hP S lam hh hh'
  have hmemb : (1 / 2 : ℝ) • h + (1 / 2 : ℝ) • h' ∈ Hset :=
    hP.convex hh hh' (by norm_num) (by norm_num) (by norm_num)
  have := hmin _ hmemb
  linarith

lemma dist_le {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlam : 0 < lam) (hhat : (Fin m → Z) → E) (hmin : IsRegMinimizerOn Hset f lam hhat)
    (S : Fin m → Z) (i : Fin m) (z' : Z) :
    ‖hhat S - hhat (Function.update S i z')‖ ≤ 4 * L / (lam * m) := by
  set S' := Function.update S i z' with hS'
  set h := hhat S with hh
  set h' := hhat S' with hh'
  have hmem : h ∈ Hset := (hmin S).1
  have hmem' : h' ∈ Hset := (hmin S').1
  have g1 := reg_gap hP S lam hmem hmem' (hmin S).2
  have g2 := reg_gap hP S' lam hmem' hmem (hmin S').2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : 0 ≤ L := hP.lipschitz_nonneg
  have hd' : ‖h' - h‖ = ‖h - h'‖ := norm_sub_rev _ _
  have hd0 : 0 ≤ ‖h - h'‖ := norm_nonneg _
  have l1 := hP.lipschitz (S i) h' hmem' h hmem
  have l2 := hP.lipschitz z' h' hmem' h hmem
  rw [hd'] at l1 l2 g2
  have e1 := empRisk_update (f := f) S i z' h
  have e2 := empRisk_update (f := f) S i z' h'
  generalize ‖h - h'‖ = d at *
  have hsum : lam / 2 * d ^ 2 ≤ ((f h' (S i) - f h (S i)) - (f h' z' - f h z')) / m := by
    have : regObjective f lam S h' - regObjective f lam S h +
        (regObjective f lam S' h - regObjective f lam S' h') =
        ((f h' (S i) - f h (S i)) - (f h' z' - f h z')) / m := by
      unfold regObjective
      rw [e1, e2]
      ring
    linarith
  have hbound : ((f h' (S i) - f h (S i)) - (f h' z' - f h z')) / m ≤ 2 * L * d / m := by
    apply div_le_div_of_nonneg_right _ hm'.le
    have a1 := (abs_le.mp l1).2
    have a2 := (abs_le.mp l2).1
    linarith
  have key : lam / 2 * d ^ 2 ≤ 2 * L * d / m := hsum.trans hbound
  rw [le_div_iff₀ (mul_pos hlam hm')]
  rcases hd0.eq_or_lt with h0 | hpos
  · rw [← h0]; nlinarith
  · have : lam / 2 * d ^ 2 * m ≤ 2 * L * d := by
      have := mul_le_mul_of_nonneg_right key hm'.le
      rwa [div_mul_cancel₀ _ hm'.ne'] at this
    nlinarith

lemma loss_stab {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlam : 0 < lam) (hhat : (Fin m → Z) → E) (hmin : IsRegMinimizerOn Hset f lam hhat)
    (S : Fin m → Z) (i : Fin m) (z' z : Z) :
    |f (hhat (Function.update S i z')) z - f (hhat S) z| ≤ 4 * L ^ 2 / (lam * m) := by
  have hd := dist_le hP hm hlam hhat hmin S i z'
  have hl := hP.lipschitz z (hhat (Function.update S i z')) (hmin _).1 (hhat S) (hmin S).1
  rw [norm_sub_rev] at hd
  have hL : 0 ≤ L := hP.lipschitz_nonneg
  calc |f (hhat (Function.update S i z')) z - f (hhat S) z|
      ≤ L * ‖hhat (Function.update S i z') - hhat S‖ := hl
    _ ≤ L * (4 * L / (lam * m)) := mul_le_mul_of_nonneg_left hd hL
    _ = 4 * L ^ 2 / (lam * m) := by ring

end Deterministic

section MeasurePart

variable {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma abs_risk_le' {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (D : Measure Z) [IsProbabilityMeasure D]
    {h : E} (hh : h ∈ Hset) : |risk f D h| ≤ C := by
  unfold risk
  have := norm_integral_le_of_norm_le_const (μ := D) (f := f h) (C := C)
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hP.loss_bounded h hh z)
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma abs_empRisk_le' {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z)
    {h : E} (hh : h ∈ Hset) : |empRisk f S h| ≤ C := by
  unfold empRisk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [abs_div, abs_of_pos hm', div_le_iff₀ hm']
  calc |∑ i, f h (S i)| ≤ ∑ i, |f h (S i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, C := Finset.sum_le_sum fun i _ => hP.loss_bounded h hh _
    _ = C * m := by simp [mul_comm]

lemma integral_empRisk' {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (hm : 1 ≤ m) {h : E} (hh : h ∈ Hset) :
    ∫ S, empRisk f S h ∂(Measure.pi fun _ : Fin m => D) = risk f D h := by
  have hm' : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    exact this.ne'
  have hi : ∀ i : Fin m, Integrable (fun S : Fin m → Z => f h (S i))
      (Measure.pi fun _ : Fin m => D) := fun i =>
    integrable_of_abs_le' ((hP.measurable h hh).comp (measurable_pi_apply i)) C
      fun S => hP.loss_bounded h hh _
  have h1 : ∀ i : Fin m, ∫ S, f h (S i) ∂(Measure.pi fun _ : Fin m => D) = risk f D h :=
    fun i => integral_comp_eval (hP.measurable h hh).aestronglyMeasurable
  have hsum : ∫ S, ∑ i, f h (S i) ∂(Measure.pi fun _ : Fin m => D)
      = ∑ i, ∫ S, f h (S i) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_finsetSum _ fun i _ => hi i
  unfold empRisk
  rw [integral_div, hsum, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel_left₀ _ hm']

lemma gen_le {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (hm : 1 ≤ m) (hhat : (Fin m → Z) → E) (hmem : ∀ S, hhat S ∈ Hset)
    (hmeas : IsMeasurableSelection f hhat) (κ : ℝ)
    (hκ : ∀ (S : Fin m → Z) (i : Fin m) (z' : Z),
      |f (hhat (Function.update S i z')) z' - f (hhat S) z'| ≤ κ) :
    ∫ S, (risk f D (hhat S) - empRisk f S (hhat S)) ∂(Measure.pi fun _ : Fin m => D) ≤ κ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hW : Measurable (fun p : (Fin m → Z) × Z => f (hhat p.1) p.2) := hmeas
  have hR : Measurable (fun S : Fin m → Z => risk f D (hhat S)) :=
    (hW.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hE : Measurable (fun S : Fin m → Z => empRisk f S (hhat S)) := by
    unfold empRisk
    refine Measurable.div_const ?_ _
    refine Finset.measurable_sum _ fun i _ => ?_
    exact hW.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hRi : Integrable (fun S : Fin m → Z => risk f D (hhat S)) (Measure.pi fun _ : Fin m => D) :=
    integrable_of_abs_le' hR C fun S => abs_risk_le' hP D (hmem S)
  have hEi : Integrable (fun S : Fin m → Z => empRisk f S (hhat S))
      (Measure.pi fun _ : Fin m => D) :=
    integrable_of_abs_le' hE C fun S => abs_empRisk_le' hP hm S (hmem S)
  rw [integral_sub hRi hEi]
  have hWi : Integrable (fun p : (Fin m → Z) × Z => f (hhat p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    integrable_of_abs_le' hW C fun p => hP.loss_bounded _ (hmem _) _
  have hG : ∀ i : Fin m,
      Measurable (fun p : (Fin m → Z) × Z => f (hhat (Function.update p.1 i p.2)) p.2) :=
    fun i => hW.comp (measurable_update'.prodMk measurable_snd)
  have hGi : ∀ i : Fin m,
      Integrable (fun p : (Fin m → Z) × Z => f (hhat (Function.update p.1 i p.2)) p.2)
        ((Measure.pi fun _ : Fin m => D).prod D) :=
    fun i => integrable_of_abs_le' (hG i) C fun p => hP.loss_bounded _ (hmem _) _
  have hF : ∀ i : Fin m, Measurable (fun S : Fin m → Z => f (hhat S) (S i)) :=
    fun i => hW.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hFi : ∀ i : Fin m,
      Integrable (fun S : Fin m → Z => f (hhat S) (S i)) (Measure.pi fun _ : Fin m => D) :=
    fun i => integrable_of_abs_le' (hF i) C fun S => hP.loss_bounded _ (hmem _) _
  have hswap : ∀ i : Fin m,
      ∫ p, f (hhat (Function.update p.1 i p.2)) p.2 ∂((Measure.pi fun _ : Fin m => D).prod D)
        = ∫ S, f (hhat S) (S i) ∂(Measure.pi fun _ : Fin m => D) := by
    intro i
    have hmp := swap_mp D i
    have hF' : Measurable (fun p : (Fin m → Z) × Z => f (hhat p.1) (p.1 i)) :=
      (hF i).comp measurable_fst
    have h := integral_map (μ := (Measure.pi fun _ : Fin m => D).prod D)
      hmp.measurable.aemeasurable (f := fun p : (Fin m → Z) × Z => f (hhat p.1) (p.1 i))
      (by rw [hmp.map_eq]; exact hF'.aestronglyMeasurable)
    rw [hmp.map_eq] at h
    have h2 : ∫ p, f (hhat p.1) (p.1 i) ∂((Measure.pi fun _ : Fin m => D).prod D)
        = ∫ S, f (hhat S) (S i) ∂(Measure.pi fun _ : Fin m => D) := by
      have := integral_fun_fst (μ := Measure.pi fun _ : Fin m => D) (ν := D)
        (fun S : Fin m → Z => f (hhat S) (S i))
      simpa using this
    rw [← h2, h]
    congr 1
    funext p
    simp
  have hRQ : ∫ p, f (hhat p.1) p.2 ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ S, risk f D (hhat S) ∂(Measure.pi fun _ : Fin m => D) := by
    rw [integral_prod _ hWi]
    rfl
  have hsumP : ∫ S, ∑ i, f (hhat S) (S i) ∂(Measure.pi fun _ : Fin m => D)
      = ∑ i, ∫ S, f (hhat S) (S i) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_finsetSum _ fun i _ => hFi i
  have hEP : ∫ S, empRisk f S (hhat S) ∂(Measure.pi fun _ : Fin m => D)
      = (∑ i, ∫ S, f (hhat S) (S i) ∂(Measure.pi fun _ : Fin m => D)) / m := by
    unfold empRisk
    rw [integral_div, hsumP]
  have hsum0 : ∫ p, ∑ i, (f (hhat p.1) p.2 - f (hhat (Function.update p.1 i p.2)) p.2)
        ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∑ i, ∫ p, (f (hhat p.1) p.2 - f (hhat (Function.update p.1 i p.2)) p.2)
        ∂((Measure.pi fun _ : Fin m => D).prod D) :=
    integral_finsetSum _ fun i _ => hWi.sub (hGi i)
  have hgi : Integrable (fun p : (Fin m → Z) × Z =>
      (∑ i, (f (hhat p.1) p.2 - f (hhat (Function.update p.1 i p.2)) p.2)) / m)
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    (integrable_finsetSum _ fun i _ => hWi.sub (hGi i)).div_const _
  have hgint : ∫ p, (∑ i, (f (hhat p.1) p.2 - f (hhat (Function.update p.1 i p.2)) p.2)) / m
        ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ S, risk f D (hhat S) ∂(Measure.pi fun _ : Fin m => D) -
        ∫ S, empRisk f S (hhat S) ∂(Measure.pi fun _ : Fin m => D) := by
    rw [integral_div, hsum0, Finset.sum_congr rfl fun i _ => integral_sub hWi (hGi i),
      Finset.sum_sub_distrib, hRQ, hEP, Finset.sum_congr rfl fun i _ => hswap i,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_div,
      mul_div_cancel_left₀ _ hm'.ne']
  have hpt : ∀ p : (Fin m → Z) × Z,
      (∑ i, (f (hhat p.1) p.2 - f (hhat (Function.update p.1 i p.2)) p.2)) / m ≤ κ := by
    intro p
    rw [div_le_iff₀ hm']
    calc ∑ i, (f (hhat p.1) p.2 - f (hhat (Function.update p.1 i p.2)) p.2)
        ≤ ∑ _i : Fin m, κ := Finset.sum_le_sum fun i _ => by
          have := hκ p.1 i p.2
          rw [abs_sub_comm] at this
          exact (le_abs_self _).trans this
      _ = κ * m := by simp [mul_comm]
  have hle := integral_mono hgi (integrable_const κ) hpt
  rw [hgint] at hle
  simpa using hle

lemma tail_bound {Hset : Set E} {f : E → Z → ℝ} {L C B : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hB : ∀ h ∈ Hset, ‖h‖ ≤ B)
    (D : Measure Z) [IsProbabilityMeasure D] {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : 1 ≤ m)
    (hhat : (Fin m → Z) → E) (hmin : IsRegMinimizerOn Hset f lam hhat)
    (hmeas : IsMeasurableSelection f hhat) {t η : ℝ} (ht : lam * B ^ 2 / 2 < t) (hη : 0 < η) :
    sampleLaw D m {S | t < risk f D (hhat S) - optRiskOn Hset f D} ≤
      ENNReal.ofReal ((4 * L ^ 2 / (lam * m) + η) / (t - lam * B ^ 2 / 2)) := by
  have : Nonempty Hset := hP.nonempty.to_subtype
  have hprob : IsProbabilityMeasure (sampleLaw D m) := by
    unfold sampleLaw; infer_instance
  have hmem : ∀ S, hhat S ∈ Hset := fun S => (hmin S).1
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 < t - lam * B ^ 2 / 2 := by linarith
  -- the regularised population objective and its infimum
  let R : Hset → ℝ := fun h => risk f D (h : E) + lam / 2 * ‖(h : E)‖ ^ 2
  have hRbdd : BddBelow (Set.range R) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨h, rfl⟩
    have h1 := (abs_le.mp (abs_risk_le' hP D h.2)).1
    have h2 : 0 ≤ lam / 2 * ‖(h : E)‖ ^ 2 := by positivity
    show -C ≤ risk f D (h : E) + lam / 2 * ‖(h : E)‖ ^ 2
    linarith
  have hFbdd : BddBelow (Set.range fun h : Hset => risk f D (h : E)) :=
    ⟨-C, by
      rintro _ ⟨h, rfl⟩
      exact (abs_le.mp (abs_risk_le' hP D h.2)).1⟩
  obtain ⟨hs, hhs⟩ : ∃ h : Hset, R h < (⨅ h, R h) + η :=
    exists_lt_of_ciInf_lt (by linarith)
  have hr : (⨅ h, R h) ≤ optRiskOn Hset f D + lam * B ^ 2 / 2 := by
    have : (⨅ h, R h) - lam * B ^ 2 / 2 ≤ optRiskOn Hset f D := by
      refine le_ciInf fun h => ?_
      have h1 : (⨅ h, R h) ≤ R h := ciInf_le hRbdd h
      have h2 : ‖(h : E)‖ ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hB _ h.2) 2
      have h3 : lam / 2 * ‖(h : E)‖ ^ 2 ≤ lam / 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : R h = risk f D (h : E) + lam / 2 * ‖(h : E)‖ ^ 2 := rfl
      linarith
    linarith
  have hFle : ∀ S, optRiskOn Hset f D ≤ risk f D (hhat S) := fun S =>
    ciInf_le hFbdd (⟨hhat S, hmem S⟩ : Hset)
  -- the dominating measurable function
  set hstar : E := (hs : E) with hstar_def
  have hstarmem : hstar ∈ Hset := hs.2
  let Mfun : (Fin m → Z) → ℝ := fun S =>
    (empRisk f S hstar + lam / 2 * ‖hstar‖ ^ 2) +
      (risk f D (hhat S) - empRisk f S (hhat S))
  have hW : Measurable (fun p : (Fin m → Z) × Z => f (hhat p.1) p.2) := hmeas
  have hRm : Measurable (fun S : Fin m → Z => risk f D (hhat S)) :=
    (hW.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hEm : Measurable (fun S : Fin m → Z => empRisk f S (hhat S)) := by
    unfold empRisk
    refine Measurable.div_const ?_ _
    refine Finset.measurable_sum _ fun i _ => ?_
    exact hW.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hCm : Measurable (fun S : Fin m → Z => empRisk f S hstar) := by
    unfold empRisk
    refine Measurable.div_const ?_ _
    exact Finset.measurable_sum _ fun i _ =>
      (hP.measurable hstar hstarmem).comp (measurable_pi_apply i)
  have hRi : Integrable (fun S : Fin m → Z => risk f D (hhat S)) (sampleLaw D m) :=
    integrable_of_abs_le' hRm C fun S => abs_risk_le' hP D (hmem S)
  have hEi : Integrable (fun S : Fin m → Z => empRisk f S (hhat S)) (sampleLaw D m) :=
    integrable_of_abs_le' hEm C fun S => abs_empRisk_le' hP hm S (hmem S)
  have hCi : Integrable (fun S : Fin m → Z => empRisk f S hstar) (sampleLaw D m) :=
    integrable_of_abs_le' hCm C fun S => abs_empRisk_le' hP hm S hstarmem
  have hMi : Integrable Mfun (sampleLaw D m) :=
    (hCi.add (integrable_const _)).add (hRi.sub hEi)
  have hMge : ∀ S, risk f D (hhat S) + lam / 2 * ‖hhat S‖ ^ 2 ≤ Mfun S := by
    intro S
    have h1 := (hmin S).2 hstar hstarmem
    unfold regObjective at h1
    show _ ≤ (empRisk f S hstar + lam / 2 * ‖hstar‖ ^ 2) +
      (risk f D (hhat S) - empRisk f S (hhat S))
    linarith
  have hMr : ∀ S, (⨅ h, R h) ≤ Mfun S := by
    intro S
    have h2 : (⨅ h, R h) ≤ R ⟨hhat S, hmem S⟩ := ciInf_le hRbdd _
    have h3 := hMge S
    have h4 : R ⟨hhat S, hmem S⟩ = risk f D (hhat S) + lam / 2 * ‖hhat S‖ ^ 2 := rfl
    linarith
  -- expectation of Mfun
  have hκ : ∀ (S : Fin m → Z) (i : Fin m) (z' : Z),
      |f (hhat (Function.update S i z')) z' - f (hhat S) z'| ≤ 4 * L ^ 2 / (lam * m) :=
    fun S i z' => loss_stab hP hm hlam hhat hmin S i z' z'
  have hgen := gen_le hP D hm hhat hmem hmeas _ hκ
  have hIntM : ∫ S, Mfun S ∂(sampleLaw D m) ≤ R hs + 4 * L ^ 2 / (lam * m) := by
    have e1 : ∫ S, Mfun S ∂(sampleLaw D m) =
        (∫ S, empRisk f S hstar ∂(sampleLaw D m) + lam / 2 * ‖hstar‖ ^ 2) +
          ∫ S, (risk f D (hhat S) - empRisk f S (hhat S)) ∂(sampleLaw D m) := by
      show ∫ S, ((empRisk f S hstar + lam / 2 * ‖hstar‖ ^ 2) +
        (risk f D (hhat S) - empRisk f S (hhat S))) ∂(sampleLaw D m) = _
      have hA : Integrable (fun S : Fin m → Z => empRisk f S hstar + lam / 2 * ‖hstar‖ ^ 2)
          (sampleLaw D m) := hCi.add (integrable_const _)
      have hG : Integrable (fun S : Fin m → Z => risk f D (hhat S) - empRisk f S (hhat S))
          (sampleLaw D m) := hRi.sub hEi
      rw [integral_add hA hG, integral_add hCi (integrable_const _)]
      simp
    have e2 : ∫ S, empRisk f S hstar ∂(sampleLaw D m) = risk f D hstar :=
      integral_empRisk' hP D hm hstarmem
    have e3 : R hs = risk f D hstar + lam / 2 * ‖hstar‖ ^ 2 := rfl
    unfold sampleLaw at hgen e1 e2 ⊢
    linarith
  -- Markov
  have hnn : (0 : (Fin m → Z) → ℝ) ≤ᵐ[sampleLaw D m] fun S => Mfun S - ⨅ h, R h :=
    ae_of_all _ fun S => by simp only [Pi.zero_apply]; linarith [hMr S]
  have hMk := mul_meas_ge_le_integral_of_nonneg hnn (hMi.sub (integrable_const _))
    (t - lam * B ^ 2 / 2)
  have hint : ∫ S, (Mfun S - ⨅ h, R h) ∂(sampleLaw D m) =
      ∫ S, Mfun S ∂(sampleLaw D m) - ⨅ h, R h := by
    rw [integral_sub hMi (integrable_const _)]
    simp
  rw [hint] at hMk
  have hincl : {S | t < risk f D (hhat S) - optRiskOn Hset f D} ⊆
      {S | t - lam * B ^ 2 / 2 ≤ Mfun S - ⨅ h, R h} := by
    intro S hS
    change t < risk f D (hhat S) - optRiskOn Hset f D at hS
    change t - lam * B ^ 2 / 2 ≤ Mfun S - ⨅ h, R h
    have h1 := hMge S
    have h2 : 0 ≤ lam / 2 * ‖hhat S‖ ^ 2 := by positivity
    linarith
  have hbd : (t - lam * B ^ 2 / 2) * (sampleLaw D m).real
      {S | t - lam * B ^ 2 / 2 ≤ Mfun S - ⨅ h, R h} ≤ 4 * L ^ 2 / (lam * m) + η := by
    linarith
  have hreal : (sampleLaw D m).real {S | t - lam * B ^ 2 / 2 ≤ Mfun S - ⨅ h, R h} ≤
      (4 * L ^ 2 / (lam * m) + η) / (t - lam * B ^ 2 / 2) := by
    rw [le_div_iff₀ ha]
    linarith
  calc sampleLaw D m {S | t < risk f D (hhat S) - optRiskOn Hset f D}
      ≤ sampleLaw D m {S | t - lam * B ^ 2 / 2 ≤ Mfun S - ⨅ h, R h} := measure_mono hincl
    _ = ENNReal.ofReal ((sampleLaw D m).real
          {S | t - lam * B ^ 2 / 2 ≤ Mfun S - ⨅ h, R h}) :=
        (ofReal_measureReal (by finiteness)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end MeasurePart

end P44d4642b

open LearnStability.ConvexSCO MeasureTheory in
theorem solution {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Hset : Set E} {f : E → Z → ℝ} {L C B : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hL : 0 < L) (hBpos : 0 < B)
    (hB : ∀ h ∈ Hset, ‖h‖ ≤ B) (D : Measure Z) [IsProbabilityMeasure D]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {m : ℕ} (hm : 1 ≤ m)
    (hhat : (Fin m → Z) → E)
    (hmin : IsRegMinimizerOn Hset f (Real.sqrt (16 * L ^ 2 / (δ * B ^ 2 * m))) hhat)
    (hmeas : IsMeasurableSelection f hhat) :
    sampleLaw D m {S | 4 * Real.sqrt (L ^ 2 * B ^ 2 / (δ * m)) * (1 + 8 / (δ * m)) <
        risk f D (hhat S) - optRiskOn Hset f D} ≤ ENNReal.ofReal δ := by
  have _hδ1 := hδ1
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < 16 * L ^ 2 / (δ * B ^ 2 * m) := by positivity
  set lam := Real.sqrt (16 * L ^ 2 / (δ * B ^ 2 * m)) with hlam_def
  have hlam : 0 < lam := Real.sqrt_pos.mpr hpos
  have hsq : lam ^ 2 = 16 * L ^ 2 / (δ * B ^ 2 * m) := Real.sq_sqrt hpos.le
  have hL2 : L ^ 2 = lam ^ 2 * (δ * B ^ 2 * m) / 16 := by
    rw [hsq]; field_simp
  have hT : lam * B ^ 2 = 4 * Real.sqrt (L ^ 2 * B ^ 2 / (δ * m)) := by
    have h1 : (lam * B ^ 2) ^ 2 = 4 ^ 2 * (L ^ 2 * B ^ 2 / (δ * m)) := by
      have : (lam * B ^ 2) ^ 2 = lam ^ 2 * B ^ 4 := by ring
      rw [this, hsq]
      field_simp
      ring
    have h2 : 0 ≤ L ^ 2 * B ^ 2 / (δ * m) := by positivity
    have h3 : 0 ≤ 4 * Real.sqrt (L ^ 2 * B ^ 2 / (δ * m)) := by positivity
    have h4 : (4 * Real.sqrt (L ^ 2 * B ^ 2 / (δ * m))) ^ 2 = 4 ^ 2 * (L ^ 2 * B ^ 2 / (δ * m)) := by
      rw [mul_pow, Real.sq_sqrt h2]
    exact (sq_eq_sq₀ (by positivity) h3).mp (h1.trans h4.symm)
  have hge : lam * B ^ 2 ≤ 4 * Real.sqrt (L ^ 2 * B ^ 2 / (δ * m)) * (1 + 8 / (δ * m)) := by
    rw [← hT]
    have : 0 ≤ lam * B ^ 2 * (8 / (δ * m)) := by positivity
    nlinarith
  have hlt : lam * B ^ 2 / 2 < 4 * Real.sqrt (L ^ 2 * B ^ 2 / (δ * m)) * (1 + 8 / (δ * m)) := by
    have : 0 < lam * B ^ 2 := by positivity
    linarith
  have hη : 0 < lam * δ * B ^ 2 / 4 := by positivity
  refine (P44d4642b.tail_bound hP hB D hlam hm hhat hmin hmeas hlt hη).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hκ : 4 * L ^ 2 / (lam * m) = lam * δ * B ^ 2 / 4 := by
    rw [hL2]; field_simp; norm_num
  rw [hκ, div_le_iff₀ (by linarith)]
  have h1 : 0 < lam * B ^ 2 := by positivity
  nlinarith [mul_pos hδ0 h1]
