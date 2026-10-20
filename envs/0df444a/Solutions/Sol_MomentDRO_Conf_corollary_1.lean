-- Prove2me | solution 1 for MomentDRO.Conf.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T22:08:10.6943+00:00
-- url     : https://prove2.me/submissions/512ee60b-74bf-4cba-9861-285dcf28603f

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace PC3a

lemma int_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

lemma abs_integral_le_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : |∫ x, F x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := C)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  simpa [Real.norm_eq_abs] using this

/-- Hoeffding step: a measurable function with oscillation at most `c`. -/
lemma hoeff_step {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (G : Ω → ℝ) (hG : Measurable G) (c B : ℝ) (hc : 0 ≤ c) (hB : ∀ z, |G z| ≤ B)
    (hosc : ∀ z z', G z' - G z ≤ c) (t : ℝ) :
    ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 8 * t ^ 2) := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
  have hbdd : BddBelow (Set.range G) := ⟨-B, by
    rintro _ ⟨z, rfl⟩; have := hB z; rw [abs_le] at this; linarith⟩
  set A := ⨅ z, G z with hA
  have hmem : ∀ z, G z ∈ Set.Icc A (A + c) := by
    intro z
    refine ⟨ciInf_le hbdd z, ?_⟩
    have : G z - c ≤ A := le_ciInf fun z' => by have := hosc z' z; linarith
    linarith
  have hs := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := G) (a := A) (b := A + c)
    hG.aemeasurable (Filter.Eventually.of_forall hmem)
  have h1 := hs.mgf_le t
  have hcoe : (((‖(A + c) - A‖₊ / 2) ^ 2 : NNReal) : ℝ) = c ^ 2 / 4 := by
    have : (A + c) - A = c := by ring
    rw [this]
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg hc]
    ring
  rw [hcoe] at h1
  unfold mgf at h1
  calc ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 4 * t ^ 2 / 2) := h1
    _ = Real.exp (c ^ 2 / 8 * t ^ 2) := by ring_nf

/-- McDiarmid's inequality, mgf form, uniform difference bound `c`. -/
theorem mcd_mgf {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (c B : ℝ) (hc : 0 ≤ c) : ∀ (n : ℕ) (f : (Fin n → Ω) → ℝ), Measurable f →
    (∀ S, |f S| ≤ B) → (∀ S i z, |f (Function.update S i z) - f S| ≤ c) → ∀ t : ℝ,
    ∫ S, Real.exp (t * (f S - ∫ S', f S' ∂(Measure.pi fun _ => ν))) ∂(Measure.pi fun _ => ν)
      ≤ Real.exp (n * c ^ 2 / 8 * t ^ 2) := by
  intro n
  induction n with
  | zero =>
    intro f _ _ _ t
    have hfS : ∀ S, f S = f default := fun S => congrArg f (Subsingleton.elim _ _)
    simp [hfS]
  | succ n ih =>
    intro f hf hB hdiff t
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => ν)
        (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have hmps := hmp.symm e
    set g : Ω → (Fin n → Ω) → ℝ := fun z w => f (Fin.cons z w) with hg
    have hge : ∀ p : Ω × (Fin n → Ω), f (e.symm p) = g p.1 p.2 := by
      intro p; simp [g, e]; try rfl
    have hgm : Measurable (Function.uncurry g) := by
      have : Function.uncurry g = fun p => f (e.symm p) := by
        funext p; rw [hge p]; rfl
      rw [this]; exact hf.comp e.symm.measurable
    have hgB : ∀ z w, |g z w| ≤ B := fun z w => hB _
    set hw : (Fin n → Ω) → ℝ := fun w => ∫ z, g z w ∂ν with hhw
    have hwm : Measurable hw :=
      (StronglyMeasurable.integral_prod_left (μ := ν) hgm.stronglyMeasurable).measurable
    have hwB : ∀ w, |hw w| ≤ B := fun w => abs_integral_le_of_bdd ν _ B fun z => hgB z w
    have hgz : ∀ w, Measurable fun z => g z w := fun w => hgm.comp (measurable_id.prodMk measurable_const)
    have hwdiff : ∀ w j y, |hw (Function.update w j y) - hw w| ≤ c := by
      intro w j y
      simp only [hw]
      rw [← integral_sub (int_of_bdd ν _ (hgz _) B fun z => hgB z _)
        (int_of_bdd ν _ (hgz _) B fun z => hgB z _)]
      refine abs_integral_le_of_bdd ν _ c fun z => ?_
      simp only [g, Fin.cons_update]
      exact hdiff _ _ _
    have hih := ih hw hwm hwB hwdiff t
    -- the mean
    have hint_f : Integrable (fun p : Ω × (Fin n → Ω) => g p.1 p.2) (ν.prod (Measure.pi fun _ => ν)) :=
      int_of_bdd _ _ hgm B fun p => hgB p.1 p.2
    have hmean : ∫ S, f S ∂(Measure.pi fun _ => ν) = ∫ w, hw w ∂(Measure.pi fun _ => ν) := by
      rw [← hmps.integral_comp' (g := f)]
      simp_rw [hge]
      rw [integral_prod_symm _ hint_f]
    obtain ⟨m, hm⟩ : ∃ m, m = ∫ S, f S ∂(Measure.pi fun _ => ν) := ⟨_, rfl⟩
    rw [← hm]
    rw [← hm] at hmean
    have hexpm : Measurable fun p : Ω × (Fin n → Ω) => Real.exp (t * (g p.1 p.2 - m)) :=
      Real.measurable_exp.comp (measurable_const.mul (hgm.sub measurable_const))
    have hint_e : Integrable (fun p : Ω × (Fin n → Ω) => Real.exp (t * (g p.1 p.2 - m)))
        (ν.prod (Measure.pi fun _ => ν)) :=
      int_of_bdd _ _ hexpm (Real.exp (|t| * (B + |m|))) fun p => by
        rw [abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 := hgB p.1 p.2
        calc t * (g p.1 p.2 - m) ≤ |t * (g p.1 p.2 - m)| := le_abs_self _
          _ = |t| * |g p.1 p.2 - m| := abs_mul _ _
          _ ≤ |t| * (B + |m|) := by
            gcongr
            calc |g p.1 p.2 - m| ≤ |g p.1 p.2| + |m| := abs_sub _ _
              _ ≤ B + |m| := by linarith
    have hstep : ∀ w, ∫ z, Real.exp (t * (g z w - m)) ∂ν ≤
        Real.exp (t * (hw w - m)) * Real.exp (c ^ 2 / 8 * t ^ 2) := by
      intro w
      have hosc : ∀ z z', g z' w - g z w ≤ c := by
        intro z z'
        have := hdiff (Fin.cons z w) 0 z'
        rw [Fin.update_cons_zero] at this
        exact (abs_le.mp this).2
      have hh := hoeff_step ν (fun z => g z w) (hgz w) c B hc (fun z => hgB z w) hosc t
      have : ∀ z, Real.exp (t * (g z w - m)) =
          Real.exp (t * (hw w - m)) * Real.exp (t * (g z w - ∫ z', g z' w ∂ν)) := by
        intro z; rw [← Real.exp_add]; congr 1; simp only [hw]; ring
      simp_rw [this]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    calc ∫ S, Real.exp (t * (f S - m)) ∂(Measure.pi fun _ => ν)
        = ∫ w, ∫ z, Real.exp (t * (g z w - m)) ∂ν ∂(Measure.pi fun _ => ν) := by
          rw [← hmps.integral_comp' (g := fun S => Real.exp (t * (f S - m)))]
          simp_rw [hge]
          rw [integral_prod_symm _ hint_e]
      _ ≤ ∫ w, Real.exp (t * (hw w - m)) * Real.exp (c ^ 2 / 8 * t ^ 2)
            ∂(Measure.pi fun _ => ν) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
            integral_nonneg fun z => (Real.exp_pos _).le) ?_ (Filter.Eventually.of_forall hstep)
          refine Integrable.mul_const ?_ _
          refine int_of_bdd _ _ (Real.measurable_exp.comp
            (measurable_const.mul (hwm.sub measurable_const))) (Real.exp (|t| * (B + |m|))) fun w => ?_
          rw [abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          have h1 := hwB w
          calc t * (hw w - m) ≤ |t * (hw w - m)| := le_abs_self _
            _ = |t| * |hw w - m| := abs_mul _ _
            _ ≤ |t| * (B + |m|) := by
              gcongr
              calc |hw w - m| ≤ |hw w| + |m| := abs_sub _ _
                _ ≤ B + |m| := by linarith
      _ = (∫ w, Real.exp (t * (hw w - ∫ w', hw w' ∂(Measure.pi fun _ => ν)))
            ∂(Measure.pi fun _ => ν)) * Real.exp (c ^ 2 / 8 * t ^ 2) := by
          rw [integral_mul_const, ← hmean]
      _ ≤ Real.exp (n * c ^ 2 / 8 * t ^ 2) * Real.exp (c ^ 2 / 8 * t ^ 2) :=
          mul_le_mul_of_nonneg_right hih (Real.exp_pos _).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * c ^ 2 / 8 * t ^ 2) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring

lemma int_exp_of_bdd {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (t : ℝ) :
    Integrable (fun x => Real.exp (t * f x)) ν := by
  refine Integrable.of_bound ((hf.const_mul t).exp.aestronglyMeasurable) (Real.exp (|t| * B))
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * f x ≤ |t * f x| := le_abs_self _
    _ = |t| * |f x| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)

section Hilb

variable {S : Type} [MeasurableSpace S]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

theorem cross_zero (P : Measure S) [IsProbabilityMeasure P] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (ζ : S → H) (hζm : Measurable ζ) (R : ℝ) (hR : 0 ≤ R) (hζb : ∀ s, ‖ζ s‖ ≤ R)
    (hζ0 : ∀ u : H, ∫ s, inner (𝕜 := ℝ) u (ζ s) ∂P = 0) :
    ∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂(Measure.pi fun _ : Fin n => P) = 0 := by
  have hind : IndepFun (fun D : Fin n → S => D i) (fun D => D j)
      (Measure.pi fun _ : Fin n => P) :=
    (iIndepFun_pi (X := fun _ => (id : S → S)) (fun _ => aemeasurable_id)).indepFun hij
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 hind
  have hev : ∀ k : Fin n, (Measure.pi fun _ : Fin n => P).map (fun D => D k) = P :=
    fun k => (measurePreserving_eval (fun _ : Fin n => P) k).map_eq
  have hgm : Measurable fun p : S × S => inner (𝕜 := ℝ) (ζ p.1) (ζ p.2) :=
    (hζm.comp measurable_fst).inner (hζm.comp measurable_snd)
  have hgI : Integrable (fun p : S × S => inner (𝕜 := ℝ) (ζ p.1) (ζ p.2)) (P.prod P) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable (R * R) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    calc |inner (𝕜 := ℝ) (ζ p.1) (ζ p.2)| ≤ ‖ζ p.1‖ * ‖ζ p.2‖ := abs_real_inner_le_norm _ _
      _ ≤ R * R := mul_le_mul (hζb _) (hζb _) (norm_nonneg _) hR
  have e1 : (∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂(Measure.pi fun _ : Fin n => P)) =
      ∫ p, inner (𝕜 := ℝ) (ζ p.1) (ζ p.2)
        ∂((Measure.pi fun _ : Fin n => P).map (fun D => (D i, D j))) := by
    rw [integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
      hgm.aestronglyMeasurable]
  rw [e1, hmap, hev, hev, integral_prod _ hgI]
  simp only
  have : ∀ a : S, ∫ b, inner (𝕜 := ℝ) (ζ a) (ζ b) ∂P = 0 := fun a => hζ0 (ζ a)
  simp [this]

/-- sharp concentration of the norm of a centred Hilbert-space sample mean. -/
theorem conc (P : Measure S) [IsProbabilityMeasure P] (ζ : S → H) (hζm : Measurable ζ)
    (R : ℝ) (hR : 0 ≤ R) (hζb : ∀ s, ‖ζ s‖ ≤ R)
    (hζ0 : ∀ u : H, ∫ s, inner (𝕜 := ℝ) u (ζ s) ∂P = 0) (n : ℕ) (hn : 0 < n)
    (r : ℝ) (hr : 0 ≤ r) :
    (Measure.pi fun _ : Fin n => P).real
      {D | R / Real.sqrt n + r ≤ ‖(1 / (n : ℝ)) • ∑ i, ζ (D i)‖} ≤
      Real.exp (-r ^ 2 / (2 * (R ^ 2 / n))) := by
  set μn := Measure.pi fun _ : Fin n => P with hμn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set Z : (Fin n → S) → ℝ := fun D => ‖(1 / (n : ℝ)) • ∑ i, ζ (D i)‖ with hZ
  have hsumm : Measurable fun D : Fin n → S => ∑ i, ζ (D i) :=
    Finset.measurable_sum _ fun i _ => hζm.comp (measurable_pi_apply i)
  have hZm : Measurable Z := (hsumm.const_smul _).norm
  have hZB : ∀ D, |Z D| ≤ R := by
    intro D
    rw [abs_of_nonneg (norm_nonneg _)]
    show ‖(1 / (n : ℝ)) • ∑ i, ζ (D i)‖ ≤ R
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : ‖∑ i, ζ (D i)‖ ≤ n * R := by
      calc ‖∑ i, ζ (D i)‖ ≤ ∑ i : Fin n, ‖ζ (D i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin n, R := Finset.sum_le_sum fun i _ => hζb _
        _ = n * R := by simp
    rw [one_div, inv_mul_le_iff₀ hnpos]; linarith
  have hZd : ∀ (D : Fin n → S) (i : Fin n) (z : S),
      |Z (Function.update D i z) - Z D| ≤ 2 * R / n := by
    intro D i z
    have hdiff : (1 / (n : ℝ)) • ∑ j, ζ (Function.update D i z j) -
        (1 / (n : ℝ)) • ∑ j, ζ (D j) = (1 / (n : ℝ)) • (ζ z - ζ (D i)) := by
      have : ∑ j, ζ (Function.update D i z j) - ∑ j, ζ (D j) = ζ z - ζ (D i) := by
        rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [Function.update_of_ne hj, sub_self])
          (by simp)]
        simp
      rw [← this, smul_sub]
    calc |Z (Function.update D i z) - Z D|
        ≤ ‖(1 / (n : ℝ)) • ∑ j, ζ (Function.update D i z j) -
          (1 / (n : ℝ)) • ∑ j, ζ (D j)‖ := abs_norm_sub_norm_le _ _
      _ = (1 / (n : ℝ)) * ‖ζ z - ζ (D i)‖ := by
          rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      _ ≤ (1 / (n : ℝ)) * (R + R) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add (hζb _) (hζb _))
      _ = 2 * R / n := by ring
  set m := ∫ D, Z D ∂μn with hm
  have hZeq : ∀ D, Z D ^ 2 = (1 / (n : ℝ)) ^ 2 *
      ∑ i, ∑ j, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) := by
    intro D
    rw [hZ]; simp only
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  have hpairI : ∀ i j : Fin n, Integrable (fun D : Fin n → S =>
      inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j))) μn := by
    intro i j
    refine Integrable.of_bound ((hζm.comp (measurable_pi_apply i)).inner
      (hζm.comp (measurable_pi_apply j))).aestronglyMeasurable (R * R) (ae_of_all _ fun D => ?_)
    rw [Real.norm_eq_abs]
    calc |inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j))| ≤ ‖ζ (D i)‖ * ‖ζ (D j)‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ R * R := mul_le_mul (hζb _) (hζb _) (norm_nonneg _) hR
  have hdiag : ∀ i : Fin n, ∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D i)) ∂μn ≤ R ^ 2 := by
    intro i
    have : ∀ D : Fin n → S, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D i)) ≤ R ^ 2 := fun D => by
      rw [real_inner_self_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hζb (D i)) 2
    calc ∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D i)) ∂μn ≤ ∫ _D, R ^ 2 ∂μn :=
          integral_mono (hpairI i i) (integrable_const _) this
      _ = R ^ 2 := by simp
  have hZ2 : ∫ D, Z D ^ 2 ∂μn ≤ R ^ 2 / n := by
    simp_rw [hZeq]
    rw [integral_const_mul, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hpairI i j]
    have hrow : ∀ i : Fin n, ∫ D, ∑ j, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂μn ≤ R ^ 2 := by
      intro i
      rw [integral_finsetSum _ fun j _ => hpairI i j]
      rw [Finset.sum_eq_single i (fun j _ hji =>
        cross_zero P n i j (Ne.symm hji) ζ hζm R hR hζb hζ0) (by simp)]
      exact hdiag i
    calc (1 / (n : ℝ)) ^ 2 * ∑ i, ∫ D, ∑ j, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂μn
        ≤ (1 / (n : ℝ)) ^ 2 * ∑ _i : Fin n, R ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hrow i) (by positivity)
      _ = R ^ 2 / n := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hm2 : m ^ 2 ≤ R ^ 2 / n := by
    have hvar := ProbabilityTheory.variance_nonneg Z μn
    rw [variance_eq_sub (MemLp.of_bound hZm.aestronglyMeasurable R
      (ae_of_all _ fun D => by rw [Real.norm_eq_abs]; exact hZB D))] at hvar
    simp only [Pi.pow_apply] at hvar
    rw [hm]
    linarith
  have hm0 : 0 ≤ m := integral_nonneg fun D => norm_nonneg _
  have hmb : m ≤ R / Real.sqrt n := by
    have h4 : (R / Real.sqrt n) ^ 2 = R ^ 2 / n := by
      rw [div_pow, Real.sq_sqrt hnpos.le]
    have : m ^ 2 ≤ (R / Real.sqrt n) ^ 2 := by rw [h4]; exact hm2
    exact (pow_le_pow_iff_left₀ hm0 (by positivity) (by norm_num)).1 this
  set cc : NNReal := ⟨R ^ 2 / n, by positivity⟩ with hcc
  have hccv : (cc : ℝ) = R ^ 2 / n := rfl
  have hsub : HasSubgaussianMGF (fun D => Z D - m) cc μn := by
    refine ⟨fun t => int_exp_of_bdd μn _ (hZm.sub measurable_const) (R + |m|)
      (fun D => ?_) t, fun t => ?_⟩
    · show |Z D - m| ≤ R + |m|
      have := hZB D; have h2 := abs_add_le (Z D) (-m)
      rw [abs_neg, ← sub_eq_add_neg] at h2; linarith
    · have := mcd_mgf P (2 * R / n) R (by positivity) n Z hZm hZB hZd t
      unfold mgf
      rw [hccv]
      calc ∫ D, Real.exp (t * (Z D - m)) ∂μn ≤ Real.exp (n * (2 * R / n) ^ 2 / 8 * t ^ 2) := this
        _ = Real.exp (R ^ 2 / n * t ^ 2 / 2) := by
          congr 1; field_simp; ring
  have htail := hsub.measure_ge_le hr
  rw [hccv] at htail
  refine le_trans (measureReal_mono (fun D hD => ?_)) htail
  show r ≤ Z D - m
  have hD' : R / Real.sqrt n + r ≤ Z D := hD
  linarith

end Hilb
theorem quad_eq {m N : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (v : Fin N → (Fin m → ℝ))
    (hv : A = ∑ k, Matrix.vecMulVec (v k) (star (v k))) (x : Fin m → ℝ) :
    MomentDRO.Conf.quadForm A x = ∑ k, (v k ⬝ᵥ x) ^ 2 := by
  subst hv
  have h1 : ∀ i j, (∑ k, Matrix.vecMulVec (v k) (star (v k))) i j = ∑ k, v k i * v k j := by
    intro i j
    rw [Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  have h2 : ∀ i, (Matrix.mulVec (∑ k, Matrix.vecMulVec (v k) (star (v k))) x) i =
      ∑ k, v k i * (v k ⬝ᵥ x) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [h1, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc]
  unfold MomentDRO.Conf.quadForm
  rw [dotProduct]
  simp_rw [h2, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sq, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem norm_toLp_sq {N : ℕ} (w : Fin N → ℝ) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin N))‖ ^ 2 = ∑ k, w k ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

theorem meas_toLp {N : ℕ} {α : Type} [MeasurableSpace α] (g : α → (Fin N → ℝ)) (hg : Measurable g) :
    Measurable fun a => (WithLp.toLp 2 (g a) : EuclideanSpace ℝ (Fin N)) := by
  exact (PiLp.continuous_toLp 2 _).measurable.comp hg

theorem smul_sum_toLp {N M : ℕ} (c : ℝ) (w : Fin M → Fin N → ℝ) :
    c • ∑ i, (WithLp.toLp 2 (w i) : EuclideanSpace ℝ (Fin N)) =
      WithLp.toLp 2 (c • ∑ i, w i) := by
  simp [WithLp.toLp_sum, WithLp.toLp_smul]

theorem inner_toLp_r {N : ℕ} (u : EuclideanSpace ℝ (Fin N)) (w : Fin N → ℝ) :
    inner (𝕜 := ℝ) u (WithLp.toLp 2 w) = ∑ k, w k * u k := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct]


end PC3a

set_option maxHeartbeats 800000 in
open MeasureTheory MomentDRO.Conf in
theorem solution {m M : ℕ} (P : Measure (Fin m → ℝ))
    (hP : HasSecondMoments P) (hcov : (covMat P).PosDef)
    (R : ℝ) (hA4 : Assumption4 P R) (hM : 0 < M)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤ sampleLaw P M
      {S | quadForm (covMat P)⁻¹ (empMean S - meanVec P) ≤ betaC M R δ} := by
  have := hP.1
  simp only [sampleLaw]
  set μ := meanVec P with hμ
  set A := (covMat P)⁻¹ with hAdef
  have hA : A.PosSemidef := hcov.inv.posSemidef
  obtain ⟨N, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  have hq := PC3a.quad_eq A v hv
  have hqc : Continuous fun ξ : Fin m → ℝ => quadForm A (ξ - μ) := by
    unfold quadForm; simp only [dotProduct, Matrix.mulVec, Pi.sub_apply]; fun_prop
  obtain ⟨T, hT⟩ : ∃ T : (Fin m → ℝ) → (Fin m → ℝ),
      T = fun ξ => if quadForm A (ξ - μ) ≤ R ^ 2 then ξ else μ := ⟨_, rfl⟩
  have hTm : Measurable T := by
    rw [hT]
    exact Measurable.ite (measurableSet_le hqc.measurable measurable_const) measurable_id
      measurable_const
  have hTq : ∀ ξ, quadForm A (T ξ - μ) ≤ R ^ 2 := by
    intro ξ
    rw [hT]
    dsimp only
    split_ifs with h
    · exact h
    · simp only [sub_self, quadForm, zero_dotProduct]; positivity
  have hTae : ∀ᵐ ξ ∂P, T ξ = ξ := hA4.2.mono fun ξ h => by rw [hT]; exact if_pos h
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (Fin m → ℝ) → EuclideanSpace ℝ (Fin N),
      ζ = fun ξ => WithLp.toLp 2 (fun k => v k ⬝ᵥ (T ξ - μ)) := ⟨_, rfl⟩
  have hζm : Measurable ζ := by
    rw [hζ]
    refine PC3a.meas_toLp _ (measurable_pi_lambda _ fun k => ?_)
    have : Continuous fun y : Fin m → ℝ => v k ⬝ᵥ (y - μ) := by
      simp only [dotProduct, Pi.sub_apply]; fun_prop
    exact this.measurable.comp hTm
  have hζb : ∀ ξ, ‖ζ ξ‖ ≤ R := by
    intro ξ
    have h2 : ‖ζ ξ‖ ^ 2 ≤ R ^ 2 := by
      rw [hζ]
      dsimp only
      rw [PC3a.norm_toLp_sq, ← hq]
      exact hTq ξ
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hA4.1 two_ne_zero).1 h2
  have hint : ∀ l, Integrable (fun ξ : Fin m → ℝ => ξ l) P :=
    fun l => (hP.2 l).integrable (by norm_num)
  have hcentI : ∀ l, Integrable (fun ξ => T ξ l - μ l) P := by
    intro l
    refine ((hint l).sub (integrable_const (μ l))).congr (hTae.mono fun ξ h => ?_)
    simp only [Pi.sub_apply, h]
  have hcent : ∀ l, ∫ ξ, (T ξ l - μ l) ∂P = 0 := by
    intro l
    rw [integral_congr_ae (g := fun ξ => ξ l - μ l) (hTae.mono fun ξ h => by simp only [h])]
    rw [integral_sub (hint l) (integrable_const (μ l)), integral_const]
    simp [hμ, meanVec]
  have hζ0 : ∀ u : EuclideanSpace ℝ (Fin N), ∫ ξ, inner (𝕜 := ℝ) u (ζ ξ) ∂P = 0 := by
    intro u
    simp only [hζ, PC3a.inner_toLp_r, dotProduct, Pi.sub_apply]
    rw [integral_finsetSum _ (fun k _ =>
      ((integrable_finsetSum _ fun l _ => (hcentI l).const_mul _).mul_const _))]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_mul_const, integral_finsetSum _ (fun l _ => (hcentI l).const_mul _)]
    simp [integral_const_mul, hcent]
  -- constants
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set L := Real.log (1 / δ) with hLdef
  have hL : 0 < L := Real.log_pos (one_lt_one_div hδ0 hδ1)
  set s := Real.sqrt (2 * L) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * L := Real.sq_sqrt (by positivity)
  set thr := R / Real.sqrt M * (2 + s) with hthr
  have hβ : betaC M R δ = thr ^ 2 := by
    rw [hthr, betaC, mul_pow, div_pow, Real.sq_sqrt hMpos.le]
  obtain ⟨Z, hZ⟩ : ∃ Z : (Fin M → (Fin m → ℝ)) → ℝ,
      Z = fun D => ‖(1 / (M : ℝ)) • ∑ i, ζ (D i)‖ := ⟨_, rfl⟩
  have hsumm : Measurable fun D : Fin M → (Fin m → ℝ) => ∑ i, ζ (D i) :=
    Finset.measurable_sum _ fun i _ => hζm.comp (measurable_pi_apply i)
  have hZm : Measurable Z := by
    rw [hZ]
    exact (hsumm.const_smul (1 / (M : ℝ))).norm
  have key : ∀ D : Fin M → (Fin m → ℝ), (∀ i, T (D i) = D i) →
      quadForm A (empMean D - μ) = Z D ^ 2 := by
    intro D hD
    have hemp : empMean D - μ = (1 / (M : ℝ)) • ∑ i, (D i - μ) := by
      rw [Finset.sum_sub_distrib, smul_sub, empMean]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div, inv_mul_cancel₀ hMpos.ne', one_smul]
    have hζD : ∀ i, ζ (D i) = WithLp.toLp 2 (fun k => v k ⬝ᵥ (D i - μ)) := by
      intro i; rw [hζ]; dsimp only; rw [hD i]
    rw [hZ]
    dsimp only
    simp only [hζD, PC3a.smul_sum_toLp, PC3a.norm_toLp_sq]
    rw [hq, hemp]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [dotProduct_smul, dotProduct_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hgood : ∀ᵐ D ∂(Measure.pi fun _ : Fin M => P), ∀ i, T (D i) = D i := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin M => P) i).ae hTae
  have hsub : {D | Z D ≤ thr} ≤ᵐ[Measure.pi fun _ : Fin M => P]
      {S | quadForm A (empMean S - μ) ≤ betaC M R δ} := by
    filter_upwards [hgood] with D hD
    refine fun hZD => ?_
    change Z D ≤ thr at hZD
    change quadForm A (empMean D - μ) ≤ betaC M R δ
    rw [key D hD, hβ]
    exact pow_le_pow_left₀ (by rw [hZ]; exact norm_nonneg _) hZD 2
  have htail : (Measure.pi fun _ : Fin M => P) {D | thr < Z D} ≤ ENNReal.ofReal δ := by
    by_cases hR0 : R = 0
    · have hζz : ∀ ξ, ζ ξ = 0 := fun ξ => norm_le_zero_iff.1 (hR0 ▸ hζb ξ)
      have : {D | thr < Z D} = ∅ := by
        ext D
        simp only [hZ, hζz, Finset.sum_const_zero, smul_zero, norm_zero, hthr, hR0,
          zero_div, zero_mul, lt_self_iff_false, Set.mem_setOf_eq, Set.mem_empty_iff_false]
      rw [this, measure_empty]; exact bot_le
    · have hRpos : 0 < R := lt_of_le_of_ne hA4.1 (Ne.symm hR0)
      set r := R / Real.sqrt M * (1 + s) with hr
      have hr0 : 0 ≤ r := by positivity
      have h1 := PC3a.conc P ζ hζm R hA4.1 hζb hζ0 M hM r hr0
      have hsubset : {D | thr < Z D} ⊆ {D | R / Real.sqrt M + r ≤ ‖(1 / (M : ℝ)) • ∑ i, ζ (D i)‖} := by
        intro D hD
        have hD' : thr < Z D := hD
        rw [hZ] at hD'
        have : R / Real.sqrt M + r = thr := by rw [hr, hthr]; ring
        show R / Real.sqrt M + r ≤ ‖(1 / (M : ℝ)) • ∑ i, ζ (D i)‖
        exact le_of_lt (this ▸ hD')
      have hexp : Real.exp (-r ^ 2 / (2 * (R ^ 2 / M))) ≤ δ := by
        have hsq : Real.sqrt M ^ 2 = M := Real.sq_sqrt hMpos.le
        have hsqpos : 0 < Real.sqrt M := Real.sqrt_pos.2 hMpos
        have : r ^ 2 / (2 * (R ^ 2 / M)) = (1 + s) ^ 2 / 2 := by
          rw [hr, mul_pow, div_pow, hsq]
          field_simp
        rw [neg_div, this]
        calc Real.exp (-((1 + s) ^ 2 / 2)) ≤ Real.exp (-L) := by
              apply Real.exp_le_exp.2; nlinarith
          _ = δ := by
              rw [Real.exp_neg, hLdef, Real.exp_log (by positivity), one_div, inv_inv]
      calc (Measure.pi fun _ : Fin M => P) {D | thr < Z D}
          ≤ (Measure.pi fun _ : Fin M => P)
              {D | R / Real.sqrt M + r ≤ ‖(1 / (M : ℝ)) • ∑ i, ζ (D i)‖} := measure_mono hsubset
        _ = ENNReal.ofReal ((Measure.pi fun _ : Fin M => P).real
              {D | R / Real.sqrt M + r ≤ ‖(1 / (M : ℝ)) • ∑ i, ζ (D i)‖}) :=
            (ofReal_measureReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (h1.trans hexp)
  have hcompl : (Measure.pi fun _ : Fin M => P) {D | Z D ≤ thr} =
      1 - (Measure.pi fun _ : Fin M => P) {D | thr < Z D} := by
    have : {D | Z D ≤ thr} = {D | thr < Z D}ᶜ := by ext D; simp [not_lt]
    rw [this, prob_compl_eq_one_sub (measurableSet_lt measurable_const hZm)]
  calc ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_sub _ hδ0.le, ENNReal.ofReal_one]
    _ ≤ 1 - (Measure.pi fun _ : Fin M => P) {D | thr < Z D} := tsub_le_tsub_left htail _
    _ = (Measure.pi fun _ : Fin M => P) {D | Z D ≤ thr} := hcompl.symm
    _ ≤ _ := measure_mono_ae hsub
