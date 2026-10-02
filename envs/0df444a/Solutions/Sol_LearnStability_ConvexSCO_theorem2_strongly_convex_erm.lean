-- Prove2me | solution 1 for LearnStability.ConvexSCO.theorem2_strongly_convex_erm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:58:11.583983+00:00
-- url     : https://prove2.me/submissions/69b41876-1777-4a07-ad93-0ff7d43a3bec

import Mathlib
import Definitions.Def_LearnStability_ConvexSCO_Setting
import Definitions.Def_LearnStability_ConvexSCO_Problem

set_option autoImplicit false

namespace P1699f3f3

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


omit [MeasurableSpace Z] in
lemma emp_gap {Hset : Set E} {f : E → Z → ℝ} {lam : ℝ}
    (hsc : ∀ z, StrongConvexOn Hset lam (fun h => f h z)) {m : ℕ} (hm : 1 ≤ m)
    (S : Fin m → Z) {h h' : E}
    (hh : h ∈ Hset) (hh' : h' ∈ Hset)
    (hmin : ∀ g ∈ Hset, empRisk f S h ≤ empRisk f S g) :
    lam / 4 * ‖h - h'‖ ^ 2 ≤ empRisk f S h' - empRisk f S h := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmemb : (1 / 2 : ℝ) • h + (1 / 2 : ℝ) • h' ∈ Hset :=
    (hsc (S ⟨0, by omega⟩)).1 hh hh' (by norm_num) (by norm_num) (by norm_num)
  have hmid : empRisk f S ((1 / 2 : ℝ) • h + (1 / 2 : ℝ) • h') ≤
      (empRisk f S h + empRisk f S h') / 2 - lam / 8 * ‖h - h'‖ ^ 2 := by
    unfold empRisk
    have hs : ∑ i, f ((1 / 2 : ℝ) • h + (1 / 2 : ℝ) • h') (S i) ≤
        ∑ i, ((f h (S i) + f h' (S i)) / 2 - lam / 8 * ‖h - h'‖ ^ 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := (hsc (S i)).2 hh hh' (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at this
      linarith
    have hs2 : ∑ i, ((f h (S i) + f h' (S i)) / 2 - lam / 8 * ‖h - h'‖ ^ 2) =
        ((∑ i, f h (S i)) + ∑ i, f h' (S i)) / 2 - m * (lam / 8 * ‖h - h'‖ ^ 2) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
      simp
    rw [hs2] at hs
    rw [div_le_iff₀ hm']
    have e : ((∑ i, f h (S i)) / m + (∑ i, f h' (S i)) / m) / 2 * m =
        ((∑ i, f h (S i)) + ∑ i, f h' (S i)) / 2 := by
      field_simp
    nlinarith [e]
  have := hmin _ hmemb
  linarith

lemma dist_le {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) {lam : ℝ}
    (hsc : ∀ z, StrongConvexOn Hset lam (fun h => f h z)) {m : ℕ} (hm : 1 ≤ m)
    (hlam : 0 < lam) (hhat : (Fin m → Z) → E) (hmin : IsEmpMinimizerOn Hset f hhat)
    (S : Fin m → Z) (i : Fin m) (z' : Z) :
    ‖hhat S - hhat (Function.update S i z')‖ ≤ 4 * L / (lam * m) := by
  set S' := Function.update S i z' with hS'
  set h := hhat S with hh
  set h' := hhat S' with hh'
  have hmem : h ∈ Hset := (hmin S).1
  have hmem' : h' ∈ Hset := (hmin S').1
  have g1 := emp_gap hsc hm S hmem hmem' (hmin S).2
  have g2 := emp_gap hsc hm S' hmem' hmem (hmin S').2
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
    have : empRisk f S h' - empRisk f S h +
        (empRisk f S' h - empRisk f S' h') =
        ((f h' (S i) - f h (S i)) - (f h' z' - f h z')) / m := by
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
    (hP : IsStochasticConvexProblem Hset f L C) {lam : ℝ}
    (hsc : ∀ z, StrongConvexOn Hset lam (fun h => f h z)) {m : ℕ} (hm : 1 ≤ m)
    (hlam : 0 < lam) (hhat : (Fin m → Z) → E) (hmin : IsEmpMinimizerOn Hset f hhat)
    (S : Fin m → Z) (i : Fin m) (z' z : Z) :
    |f (hhat (Function.update S i z')) z - f (hhat S) z| ≤ 4 * L ^ 2 / (lam * m) := by
  have hd := dist_le hP hsc hm hlam hhat hmin S i z'
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

lemma main_bound {Hset : Set E} {f : E → Z → ℝ} {L C lam : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hlam : 0 < lam)
    (hsc : ∀ z, StrongConvexOn Hset lam (fun h => f h z))
    (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m)
    (hhat : (Fin m → Z) → E) (hmin : IsEmpMinimizerOn Hset f hhat)
    (hmeas : IsMeasurableSelection f hhat) :
    ∫ S, (risk f D (hhat S) - optRiskOn Hset f D) ∂(sampleLaw D m) ≤
      4 * L ^ 2 / (lam * m) := by
  have : Nonempty Hset := hP.nonempty.to_subtype
  have hprob : IsProbabilityMeasure (sampleLaw D m) := by
    unfold sampleLaw; infer_instance
  have hmem : ∀ S, hhat S ∈ Hset := fun S => (hmin S).1
  set κ := 4 * L ^ 2 / (lam * m) with hκdef
  have hκ : ∀ (S : Fin m → Z) (i : Fin m) (z' : Z),
      |f (hhat (Function.update S i z')) z' - f (hhat S) z'| ≤ κ :=
    fun S i z' => loss_stab hP hsc hm hlam hhat hmin S i z' z'
  have hgen := gen_le hP D hm hhat hmem hmeas κ hκ
  have hW : Measurable (fun p : (Fin m → Z) × Z => f (hhat p.1) p.2) := hmeas
  have hRm : Measurable (fun S : Fin m → Z => risk f D (hhat S)) :=
    (hW.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hEm : Measurable (fun S : Fin m → Z => empRisk f S (hhat S)) := by
    unfold empRisk
    refine Measurable.div_const ?_ _
    refine Finset.measurable_sum _ fun i _ => ?_
    exact hW.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hRi : Integrable (fun S : Fin m → Z => risk f D (hhat S)) (sampleLaw D m) :=
    integrable_of_abs_le' hRm C fun S => abs_risk_le' hP D (hmem S)
  have hEi : Integrable (fun S : Fin m → Z => empRisk f S (hhat S)) (sampleLaw D m) :=
    integrable_of_abs_le' hEm C fun S => abs_empRisk_le' hP hm S (hmem S)
  -- for every comparator h, E[F(hhat S)] ≤ F(h) + κ
  have hcomp : ∀ h : Hset, ∫ S, risk f D (hhat S) ∂(sampleLaw D m) - κ ≤ risk f D (h : E) := by
    intro h
    have hCm : Measurable (fun S : Fin m → Z => empRisk f S (h : E)) := by
      unfold empRisk
      refine Measurable.div_const ?_ _
      exact Finset.measurable_sum _ fun i _ =>
        (hP.measurable h h.2).comp (measurable_pi_apply i)
    have hCi : Integrable (fun S : Fin m → Z => empRisk f S (h : E)) (sampleLaw D m) :=
      integrable_of_abs_le' hCm C fun S => abs_empRisk_le' hP hm S h.2
    have hle : ∫ S, empRisk f S (hhat S) ∂(sampleLaw D m) ≤
        ∫ S, empRisk f S (h : E) ∂(sampleLaw D m) :=
      integral_mono hEi hCi fun S => (hmin S).2 h h.2
    have e2 : ∫ S, empRisk f S (h : E) ∂(sampleLaw D m) = risk f D (h : E) :=
      integral_empRisk' hP D hm h.2
    have e3 : ∫ S, (risk f D (hhat S) - empRisk f S (hhat S)) ∂(sampleLaw D m) =
        ∫ S, risk f D (hhat S) ∂(sampleLaw D m) - ∫ S, empRisk f S (hhat S) ∂(sampleLaw D m) :=
      integral_sub hRi hEi
    unfold sampleLaw at hgen e2 e3 hle ⊢
    linarith
  have hopt : ∫ S, risk f D (hhat S) ∂(sampleLaw D m) - κ ≤ optRiskOn Hset f D :=
    le_ciInf hcomp
  rw [integral_sub hRi (integrable_const _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  linarith


lemma excess_nonneg {Hset : Set E} {f : E → Z → ℝ} {L C : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (D : Measure Z) [IsProbabilityMeasure D]
    {h : E} (hh : h ∈ Hset) : 0 ≤ risk f D h - optRiskOn Hset f D := by
  have hbdd : BddBelow (Set.range fun g : Hset => risk f D (g : E)) :=
    ⟨-C, by
      rintro _ ⟨g, rfl⟩
      have := abs_risk_le' hP D g.2
      exact (abs_le.mp this).1⟩
  have := ciInf_le hbdd (⟨h, hh⟩ : Hset)
  unfold optRiskOn
  linarith

lemma final {Hset : Set E} {f : E → Z → ℝ} {L C lam : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hlam : 0 < lam)
    (hsc : ∀ z, StrongConvexOn Hset lam (fun h => f h z))
    (D : Measure Z) [IsProbabilityMeasure D] {δ : ℝ} (hδ0 : 0 < δ)
    {m : ℕ} (hm : 1 ≤ m) (hhat : (Fin m → Z) → E) (hmin : IsEmpMinimizerOn Hset f hhat)
    (hmeas : IsMeasurableSelection f hhat) :
    sampleLaw D m {S | 4 * L ^ 2 / (δ * lam * m) < risk f D (hhat S) - optRiskOn Hset f D} ≤
      ENNReal.ofReal δ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hprob : IsProbabilityMeasure (sampleLaw D m) := by
    unfold sampleLaw; infer_instance
  have hmem : ∀ S, hhat S ∈ Hset := fun S => (hmin S).1
  have hL0 : 0 ≤ L := hP.lipschitz_nonneg
  rcases hL0.eq_or_lt with hL | hL
  · -- L = 0: the excess risk is pointwise ≤ 0
    subst hL
    have hempty : {S | 4 * (0:ℝ) ^ 2 / (δ * lam * m) < risk f D (hhat S) - optRiskOn Hset f D}
        = ∅ := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have : Nonempty Hset := hP.nonempty.to_subtype
      have hc : ∀ g : Hset, risk f D (hhat S) ≤ risk f D (g : E) := by
        intro g
        unfold risk
        refine le_of_eq (integral_congr_ae (ae_of_all _ fun z => ?_))
        have h1 := hP.lipschitz z (hhat S) (hmem S) g g.2
        simp only [zero_mul] at h1
        have := abs_nonpos_iff.mp h1
        linarith
      have := le_ciInf hc
      unfold optRiskOn
      norm_num
      linarith
    rw [hempty]; simp
  · -- Markov
    set c := 4 * L ^ 2 / (δ * lam * m) with hc
    have hcpos : 0 < c := by positivity
    set X : (Fin m → Z) → ℝ := fun S => risk f D (hhat S) - optRiskOn Hset f D with hX
    have hW : Measurable (fun p : (Fin m → Z) × Z => f (hhat p.1) p.2) := hmeas
    have hRm : Measurable (fun S : Fin m → Z => risk f D (hhat S)) :=
      (hW.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
    have hXi : Integrable X (sampleLaw D m) :=
      (integrable_of_abs_le' hRm C fun S => abs_risk_le' hP D (hmem S)).sub
        (integrable_const _)
    have hnn : (0 : (Fin m → Z) → ℝ) ≤ᵐ[sampleLaw D m] X :=
      ae_of_all _ fun S => excess_nonneg hP D (hmem S)
    have hMk := mul_meas_ge_le_integral_of_nonneg hnn hXi c
    have hE := main_bound hP hlam hsc D hm hhat hmin hmeas
    have hbd : c * (sampleLaw D m).real {S | c ≤ X S} ≤ c * δ := by
      have : c * δ = 4 * L ^ 2 / (lam * m) := by
        rw [hc]; field_simp
      rw [this]
      exact hMk.trans hE
    have hreal : (sampleLaw D m).real {S | c ≤ X S} ≤ δ :=
      le_of_mul_le_mul_left hbd hcpos
    calc sampleLaw D m {S | c < X S}
        ≤ sampleLaw D m {S | c ≤ X S} := measure_mono fun S (hS : c < X S) => show c ≤ X S from le_of_lt hS
      _ = ENNReal.ofReal ((sampleLaw D m).real {S | c ≤ X S}) :=
          (ofReal_measureReal (by finiteness)).symm
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hreal

end MeasurePart

end P1699f3f3

open MeasureTheory LearnStability.ConvexSCO in
theorem solution {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Hset : Set E} {f : E → Z → ℝ} {L C lam : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hlam : 0 < lam)
    (hsc : ∀ z, StrongConvexOn Hset lam (fun h => f h z))
    (D : Measure Z) [IsProbabilityMeasure D] {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {m : ℕ} (hm : 1 ≤ m) (hhat : (Fin m → Z) → E) (hmin : IsEmpMinimizerOn Hset f hhat)
    (hmeas : IsMeasurableSelection f hhat) :
    sampleLaw D m {S | 4 * L ^ 2 / (δ * lam * m) < risk f D (hhat S) - optRiskOn Hset f D} ≤
      ENNReal.ofReal δ := by
  have _h1 := hδ1
  exact P1699f3f3.final hP hlam hsc D hδ0 hm hhat hmin hmeas
