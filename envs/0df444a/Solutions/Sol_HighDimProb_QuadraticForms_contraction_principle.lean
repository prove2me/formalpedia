-- Prove2me | solution 1 for HighDimProb.QuadraticForms.contraction_principle
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:10:15.512843+00:00
-- url     : https://prove2.me/submissions/7427d02b-d63b-4e47-8869-53cb5dc89037

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace P2M_d51afd1c

/-- The sign attached to a Boolean. -/
noncomputable def sg (b : Bool) : ℝ := if b then 1 else -1

lemma sg_not (b : Bool) : sg (!b) = - sg b := by cases b <;> simp [sg]

lemma sg_inj : Function.Injective sg := by
  intro b c h
  revert h
  cases b <;> cases c <;> norm_num [sg]

/-- Flip the `j`-th coordinate of a sign vector. -/
def flipB {N : ℕ} (j : Fin N) : (Fin N → Bool) ≃ (Fin N → Bool) where
  toFun s := Function.update s j (!s j)
  invFun s := Function.update s j (!s j)
  left_inv s := by simp
  right_inv s := by simp

lemma flipB_apply {N : ℕ} (j : Fin N) (s : Fin N → Bool) (i : Fin N) :
    flipB j s i = if i = j then !s j else s i := by
  simp [flipB, Function.update_apply]

/-- Unnormalised average over sign vectors. -/
noncomputable def F {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (x : Fin N → E) (a : Fin N → ℝ) : ℝ :=
  ∑ s : Fin N → Bool, ‖∑ i, (a i * sg (s i)) • x i‖

lemma F_step {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (x : Fin N → E) (a : Fin N → ℝ) (j : Fin N) {b c : ℝ} (hb : |b| ≤ c) :
    F x (Function.update a j b) ≤ F x (Function.update a j c) := by
  have hc : 0 ≤ c := (abs_nonneg b).trans hb
  rcases hc.eq_or_lt with h0 | hpos
  · have : b = 0 := abs_nonpos_iff.mp (h0 ▸ hb)
    rw [this, ← h0]
  have hb1 := neg_abs_le b
  have hb2 := le_abs_self b
  set l : ℝ := (c + b) / (2 * c) with hl
  have hl0 : 0 ≤ l := by rw [hl]; apply div_nonneg <;> linarith
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by linarith)]; linarith
  set y : (Fin N → Bool) → E := fun s => ∑ i, (Function.update a j c i * sg (s i)) • x i
    with hy
  have key : ∀ s, ∑ i, (Function.update a j b i * sg (s i)) • x i
      = l • y s + (1 - l) • y (flipB j s) := by
    intro s
    simp only [hy, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    by_cases h : i = j
    · subst h
      rw [flipB_apply]
      simp only [Function.update_self, if_true, sg_not]
      rw [hl]
      field_simp
      ring
    · rw [flipB_apply, if_neg h]
      simp only [Function.update_of_ne h]
      ring
  have hflip : ∑ s, ‖y (flipB j s)‖ = ∑ s, ‖y s‖ :=
    Equiv.sum_comp (flipB j) (fun s => ‖y s‖)
  unfold F
  calc ∑ s : Fin N → Bool, ‖∑ i, (Function.update a j b i * sg (s i)) • x i‖
      ≤ ∑ s : Fin N → Bool, (l * ‖y s‖ + (1 - l) * ‖y (flipB j s)‖) := by
        apply Finset.sum_le_sum
        intro s _
        rw [key]
        calc _ ≤ ‖l • y s‖ + ‖(1 - l) • y (flipB j s)‖ := norm_add_le _ _
          _ = _ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hl0,
              Real.norm_of_nonneg (by linarith)]
    _ = l * ∑ s, ‖y s‖ + (1 - l) * ∑ s, ‖y (flipB j s)‖ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ s, ‖y s‖ := by rw [hflip]; ring

lemma F_le_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (x : Fin N → E) (M : ℝ) (a : Fin N → ℝ) (ha : ∀ i, |a i| ≤ M) :
    F x a ≤ F x (fun _ => M) := by
  suffices h : ∀ T : Finset (Fin N), ∀ a : Fin N → ℝ, (∀ i, |a i| ≤ M) →
      (∀ i, i ∉ T → a i = M) → F x a ≤ F x (fun _ => M) by
    exact h Finset.univ a ha (by simp)
  intro T
  refine Finset.induction_on T ?_ ?_
  · intro a _ h
    have : a = fun _ => M := funext fun i => h i (by simp)
    rw [this]
  · intro j T _ ih a ha hT
    have hM : 0 ≤ M := (abs_nonneg _).trans (ha j)
    calc F x a = F x (Function.update a j (a j)) := by rw [Function.update_eq_self]
      _ ≤ F x (Function.update a j M) := F_step x a j (ha j)
      _ ≤ _ := by
        apply ih
        · intro i
          by_cases h : i = j
          · subst h; simp [abs_of_nonneg hM]
          · rw [Function.update_of_ne h]; exact ha i
        · intro i hi
          by_cases h : i = j
          · subst h; simp
          · rw [Function.update_of_ne h]
            exact hT i (by simp [h, hi])

lemma integral_eq_sum {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (ε : Fin N → Ω → ℝ) (hε_meas : ∀ i, Measurable (ε i)) (hε_indep : iIndepFun ε P)
    (hε_rad : ∀ i, P.real {ω | ε i ω = 1} = 1 / 2 ∧ P.real {ω | ε i ω = -1} = 1 / 2)
    (g : (Fin N → ℝ) → ℝ) :
    ∫ ω, g (fun i => ε i ω) ∂P = ∑ s : Fin N → Bool, (1 / 2 : ℝ) ^ N * g (fun i => sg (s i)) := by
  set C : (Fin N → Bool) → Set Ω := fun s => ⋂ i, ε i ⁻¹' {sg (s i)} with hC
  have hCm : ∀ s, MeasurableSet (C s) := fun s =>
    MeasurableSet.iInter fun i => hε_meas i (measurableSet_singleton _)
  have hCP : ∀ s, P.real (C s) = (1 / 2) ^ N := by
    intro s
    have h := hε_indep.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun i => {sg (s i)}) (fun i _ => measurableSet_singleton _)
    simp only [Finset.mem_univ, Set.iInter_true] at h
    rw [measureReal_def, hC]
    simp only
    rw [h, ENNReal.toReal_prod]
    have hi : ∀ i, (P (ε i ⁻¹' {sg (s i)})).toReal = 1 / 2 := by
      intro i
      cases s i
      · exact (hε_rad i).2
      · exact (hε_rad i).1
    simp [hi]
  have hae : ∀ᵐ ω ∂P, ∀ i, ε i ω = 1 ∨ ε i ω = -1 := by
    rw [ae_all_iff]
    intro i
    have hA : MeasurableSet {ω | ε i ω = 1} := hε_meas i (measurableSet_singleton 1)
    have hB : MeasurableSet {ω | ε i ω = -1} := hε_meas i (measurableSet_singleton (-1))
    have hdisj : Disjoint {ω | ε i ω = 1} {ω | ε i ω = -1} := by
      rw [Set.disjoint_left]
      intro ω h1 h2
      simp only [Set.mem_ofPred_eq] at h1 h2
      rw [h1] at h2
      norm_num at h2
    have hU : P.real ({ω | ε i ω = 1} ∪ {ω | ε i ω = -1}) = 1 := by
      rw [measureReal_union hdisj hB, (hε_rad i).1, (hε_rad i).2]
      norm_num
    have hc : P.real ({ω | ε i ω = 1} ∪ {ω | ε i ω = -1})ᶜ = 0 := by
      rw [measureReal_compl (hA.union hB), hU]
      simp
    have hc' : P ({ω | ε i ω = 1} ∪ {ω | ε i ω = -1})ᶜ = 0 :=
      (measureReal_eq_zero_iff).mp hc
    rw [ae_iff]
    convert hc' using 2
    ext ω
    simp
  have hrep : (fun ω => g (fun i => ε i ω)) =ᵐ[P]
      fun ω => ∑ s, (C s).indicator (fun _ => g (fun i => sg (s i))) ω := by
    filter_upwards [hae] with ω hω
    set s0 : Fin N → Bool := fun i => decide (ε i ω = 1) with hs0def
    have hs0 : ∀ i, sg (s0 i) = ε i ω := by
      intro i
      rcases hω i with h | h
      · simp [hs0def, sg, h]
      · norm_num [hs0def, sg, h]
    have hmem : ∀ s, ω ∈ C s ↔ s = s0 := by
      intro s
      simp only [hC, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        funext i
        apply sg_inj
        rw [hs0 i]
        exact (h i).symm
      · rintro rfl i
        exact (hs0 i).symm
    rw [Finset.sum_eq_single s0]
    · rw [Set.indicator_of_mem ((hmem s0).2 rfl)]
      congr 1
      funext i
      exact (hs0 i).symm
    · intro s _ hs
      exact Set.indicator_of_notMem (fun h => hs ((hmem s).1 h)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [integral_congr_ae hrep, integral_finsetSum]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_indicator_const _ (hCm s), hCP s, smul_eq_mul]
  · intro s _
    exact (integrable_const _).indicator (hCm s)

end P2M_d51afd1c

open MeasureTheory ProbabilityTheory in
theorem solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : Fin N → Ω → ℝ) (hε_meas : ∀ i, Measurable (ε i)) (hε_indep : iIndepFun ε P)
    (hε_rad : ∀ i, P.real {ω | ε i ω = 1} = 1 / 2 ∧ P.real {ω | ε i ω = -1} = 1 / 2)
    (x : Fin N → E) (a : Fin N → ℝ)
    (hint1 : Integrable (fun ω => ‖∑ i, (a i * ε i ω) • x i‖) P)
    (hint2 : Integrable (fun ω => ‖∑ i, ε i ω • x i‖) P) :
    ∫ ω, ‖∑ i, (a i * ε i ω) • x i‖ ∂P ≤ (⨆ i, |a i|) * ∫ ω, ‖∑ i, ε i ω • x i‖ ∂P := by
  have h1 := P2M_d51afd1c.integral_eq_sum P ε hε_meas hε_indep hε_rad (fun y => ‖∑ i, (a i * y i) • x i‖)
  have h2 := P2M_d51afd1c.integral_eq_sum P ε hε_meas hε_indep hε_rad (fun y => ‖∑ i, y i • x i‖)
  simp only at h1 h2
  rw [h1, h2]
  have haM : ∀ i, |a i| ≤ ⨆ i, |a i| := fun i => le_ciSup (f := fun i => |a i|) (Set.finite_range _).bddAbove i
  have hM : 0 ≤ ⨆ i, |a i| := Real.iSup_nonneg fun i => abs_nonneg _
  have key := P2M_d51afd1c.F_le_const x (⨆ i, |a i|) a haM
  have hconst : P2M_d51afd1c.F x (fun _ => ⨆ i, |a i|)
      = (⨆ i, |a i|) * ∑ s : Fin N → Bool, ‖∑ i, P2M_d51afd1c.sg (s i) • x i‖ := by
    unfold P2M_d51afd1c.F
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [mul_smul, ← Finset.smul_sum]
    rw [norm_smul, Real.norm_of_nonneg hM]
  have e1 : ∑ s : Fin N → Bool, (1 / 2 : ℝ) ^ N * ‖∑ i, (a i * P2M_d51afd1c.sg (s i)) • x i‖
      = (1 / 2) ^ N * P2M_d51afd1c.F x a := by
    rw [P2M_d51afd1c.F, Finset.mul_sum]
  have e2 : (⨆ i, |a i|) * ∑ s : Fin N → Bool, (1 / 2 : ℝ) ^ N * ‖∑ i, P2M_d51afd1c.sg (s i) • x i‖
      = (1 / 2) ^ N * P2M_d51afd1c.F x (fun _ => ⨆ i, |a i|) := by
    rw [hconst, ← Finset.mul_sum]
    ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left key (by positivity)
