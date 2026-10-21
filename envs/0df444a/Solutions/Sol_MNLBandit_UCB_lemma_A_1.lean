-- Prove2me | solution 1 for MNLBandit.UCB.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:52:33.051862+00:00
-- url     : https://prove2.me/submissions/0b798d2f-40ea-41c4-a203-381433bc6ff3

import Mathlib
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_EpochLaw

set_option autoImplicit false
open MNLBandit.UCB MeasureTheory

lemma lint_pi_prod {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] (g : ι → α → ENNReal) :
    ∫⁻ x, ∏ i, g i (x i) ∂Measure.pi (fun _ : ι => μ) = ∏ i, ∫⁻ y, g i y ∂μ := by
  rw [lintegral_fintype]
  simp_rw [Measure.pi_singleton]
  simp_rw [lintegral_fintype (μ := μ)]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib]

section
variable {N : ℕ} (v : Fin N → ℝ) (S : Finset (Fin N))

lemma sum_some (hv : ∀ j, 0 ≤ v j) :
    ∑ j, choiceProb v S (some j) = (∑ j ∈ S, v j) / (1 + ∑ j ∈ S, v j) := by
  simp only [choiceProb, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]

lemma cp_nonneg (hv : ∀ j, 0 ≤ v j) (o : Option (Fin N)) : 0 ≤ choiceProb v S o := by
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => hv j)
  cases o with
  | none => simp only [choiceProb]; exact div_nonneg zero_le_one (by linarith)
  | some j =>
    simp only [choiceProb]
    split_ifs
    · exact div_nonneg (hv j) (by linarith)
    · exact le_rfl

lemma cp_sum (hv : ∀ j, 0 ≤ v j) : ∑ o, choiceProb v S o = 1 := by
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => hv j)
  have hpos : 0 < 1 + ∑ j ∈ S, v j := by linarith
  rw [Fintype.sum_option, sum_some v S hv]
  simp only [choiceProb]
  field_simp

lemma cm_univ (hv : ∀ j, 0 ≤ v j) : choiceMeasure v S Set.univ = 1 := by
  simp only [choiceMeasure, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => cp_nonneg v S hv o), cp_sum v S hv]
  simp

lemma lint_cm (g : Option (Fin N) → ENNReal) :
    ∫⁻ x, g x ∂choiceMeasure v S = ∑ o, ENNReal.ofReal (choiceProb v S o) * g o := by
  simp only [choiceMeasure]
  rw [lintegral_finset_sum_measure]
  simp [lintegral_smul_measure, lintegral_dirac]

lemma lint_prefix (hv : ∀ j, 0 ≤ v j) (g : ℕ → Option (Fin N) → ENNReal) (n : ℕ) :
    ∫⁻ ω, ∏ k ∈ Finset.range n, g k (ω k) ∂epochLaw v S =
      ∏ k ∈ Finset.range n, ∫⁻ y, g k y ∂choiceMeasure v S := by
  haveI : IsProbabilityMeasure (choiceMeasure v S) := ⟨cm_univ v S hv⟩
  have hmeas : Measurable
      (fun y : (Finset.range n) → Option (Fin N) => ∏ k : Finset.range n, g k (y k)) := by
    apply Finset.measurable_prod
    intro k _
    exact Measurable.of_discrete.comp (measurable_pi_apply k)
  have h := lintegral_restrict_infinitePi (μ := fun _ : ℕ => choiceMeasure v S)
    (s := Finset.range n) (f := fun y => ∏ k : Finset.range n, g k (y k)) hmeas
  calc ∫⁻ ω, ∏ k ∈ Finset.range n, g k (ω k) ∂epochLaw v S
      = ∫⁻ ω, ∏ k : Finset.range n, g k ((Finset.range n).restrict ω k)
          ∂Measure.infinitePi (fun _ : ℕ => choiceMeasure v S) := by
        apply lintegral_congr
        intro ω
        exact (Finset.prod_coe_sort (Finset.range n) (fun k => g k (ω k))).symm
    _ = ∫⁻ y, ∏ k : Finset.range n, g k (y k)
          ∂Measure.pi (fun _ : Finset.range n => choiceMeasure v S) := h
    _ = ∏ k : Finset.range n, ∫⁻ y, g k y ∂choiceMeasure v S :=
        lint_pi_prod (choiceMeasure v S) (fun k : Finset.range n => g k)
    _ = ∏ k ∈ Finset.range n, ∫⁻ y, g k y ∂choiceMeasure v S :=
        Finset.prod_coe_sort (Finset.range n) (fun k => ∫⁻ y, g k y ∂choiceMeasure v S)

end

theorem solution {N : ℕ} (v : Fin N → ℝ) (hv : ∀ j, 0 ≤ v j) (S : Finset (Fin N))
    (i : Fin N) (hi : i ∈ S) (θ : ℝ) (hθ : v i * (Real.exp θ - 1) < 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (epochCount i ω : ℝ))) ∂(epochLaw v S) =
      ENNReal.ofReal (1 / (1 - v i * (Real.exp θ - 1))) := by
  classical
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => hv j)
  have hpos : 0 < 1 + ∑ j ∈ S, v j := by linarith
  haveI : IsProbabilityMeasure (choiceMeasure v S) := ⟨cm_univ v S hv⟩
  have he0 : 0 < Real.exp θ := Real.exp_pos θ
  let fr : Option (Fin N) → ℝ := fun o => o.elim 0 (fun j => if j = i then Real.exp θ else 1)
  let f : Option (Fin N) → ENNReal := fun o => ENNReal.ofReal (fr o)
  let ind0 : Option (Fin N) → ENNReal := fun o => if o = none then 1 else 0
  let nn : Option (Fin N) → ENNReal := fun o => if o = none then 0 else 1
  let F : ℕ → (ℕ → Option (Fin N)) → ENNReal :=
    fun n ω => (∏ k ∈ Finset.range n, f (ω k)) * ind0 (ω n)
  have hfr0 : ∀ o, 0 ≤ fr o := by
    intro o
    cases o with
    | none => simp [fr]
    | some j =>
      simp only [fr, Option.elim]
      split_ifs
      · exact he0.le
      · exact zero_le_one
  have hA : ∑ o, choiceProb v S o * fr o =
      ((∑ j ∈ S, v j) + v i * (Real.exp θ - 1)) / (1 + ∑ j ∈ S, v j) := by
    rw [Fintype.sum_option]
    have h1 : ∀ j : Fin N, choiceProb v S (some j) * fr (some j) =
        choiceProb v S (some j) + (if j = i then choiceProb v S (some i) * (Real.exp θ - 1) else 0) := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [fr]; ring
      · simp [fr, hj]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      sum_some v S hv]
    have : fr none = 0 := by simp [fr]
    rw [this, mul_zero, zero_add]
    have h2 : choiceProb v S (some i) = v i / (1 + ∑ j ∈ S, v j) := by simp [choiceProb, hi]
    rw [h2]
    field_simp
  have hA0 : 0 ≤ ∑ o, choiceProb v S o * fr o :=
    Finset.sum_nonneg (fun o _ => mul_nonneg (cp_nonneg v S hv o) (hfr0 o))
  have hA1 : ∑ o, choiceProb v S o * fr o < 1 := by
    rw [hA, div_lt_one hpos]; linarith
  have ha : ∫⁻ y, f y ∂choiceMeasure v S = ENNReal.ofReal (∑ o, choiceProb v S o * fr o) := by
    rw [lint_cm, ENNReal.ofReal_sum_of_nonneg
      (fun o _ => mul_nonneg (cp_nonneg v S hv o) (hfr0 o))]
    apply Finset.sum_congr rfl
    intro o _
    rw [ENNReal.ofReal_mul (cp_nonneg v S hv o)]
  have hq0 : ∫⁻ y, ind0 y ∂choiceMeasure v S = ENNReal.ofReal (1 / (1 + ∑ j ∈ S, v j)) := by
    rw [lint_cm, Fintype.sum_option]
    simp [ind0, choiceProb]
  have hb : ∫⁻ y, nn y ∂choiceMeasure v S =
      ENNReal.ofReal ((∑ j ∈ S, v j) / (1 + ∑ j ∈ S, v j)) := by
    rw [lint_cm, Fintype.sum_option]
    have e0 : nn none = 0 := by simp [nn]
    have e1 : ∀ j : Fin N, ENNReal.ofReal (choiceProb v S (some j)) * nn (some j) =
        ENNReal.ofReal (choiceProb v S (some j)) := by
      intro j; simp [nn]
    simp only [e0, mul_zero, zero_add, e1]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => cp_nonneg v S hv (some j)), sum_some v S hv]
  have hmf : ∀ (g : Option (Fin N) → ENNReal) (k : ℕ),
      Measurable (fun ω : ℕ → Option (Fin N) => g (ω k)) :=
    fun g k => (Measurable.of_discrete (f := g)).comp (measurable_pi_apply k)
  -- epoch count as a sum over the first no-purchase time
  have claim1 : ∀ ω : ℕ → Option (Fin N), (∃ k, ω k = none) →
      ENNReal.ofReal (Real.exp (θ * (epochCount i ω : ℝ))) = ∑' n, F n ω := by
    intro ω h
    have hτ : ω (Nat.find h) = none := Nat.find_spec h
    have hlt : ∀ k < Nat.find h, ω k ≠ none := fun k hk => Nat.find_min h hk
    rw [tsum_eq_single (Nat.find h)]
    · simp only [F, ind0, hτ, if_true, mul_one]
      have : ∀ k ∈ Finset.range (Nat.find h),
          f (ω k) = if ω k = some i then ENNReal.ofReal (Real.exp θ) else 1 := by
        intro k hk
        have hk' := hlt k (Finset.mem_range.1 hk)
        cases hωk : ω k with
        | none => exact absurd hωk hk'
        | some j => by_cases hji : j = i <;> simp [f, fr, hji]
      rw [Finset.prod_congr rfl this, Finset.prod_ite, Finset.prod_const_one, mul_one,
        Finset.prod_const]
      unfold epochCount
      rw [dif_pos h]
      rw [← ENNReal.ofReal_pow he0.le, ← Real.exp_nat_mul]
      congr 2
      ring
    · intro n hn
      simp only [F]
      rcases lt_or_gt_of_ne hn with hlt' | hgt
      · have : ω n ≠ none := hlt n hlt'
        simp [ind0, this]
      · have : f (ω (Nat.find h)) = 0 := by simp [f, fr, hτ]
        rw [Finset.prod_eq_zero (Finset.mem_range.2 hgt) this, zero_mul]
  -- the no-purchase time is almost surely finite
  have hnull : ∀ᵐ ω ∂epochLaw v S, ∃ k, ω k = none := by
    rw [ae_iff]
    have hb1 : ENNReal.ofReal ((∑ j ∈ S, v j) / (1 + ∑ j ∈ S, v j)) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by rw [div_lt_one hpos]; linarith)
    have hle : ∀ n : ℕ, epochLaw v S {ω | ¬ ∃ k, ω k = none} ≤
        (ENNReal.ofReal ((∑ j ∈ S, v j) / (1 + ∑ j ∈ S, v j))) ^ n := by
      intro n
      have hmeas : Measurable (fun ω : ℕ → Option (Fin N) => ∏ k ∈ Finset.range n, nn (ω k)) :=
        Finset.measurable_prod _ (fun k _ => hmf nn k)
      calc epochLaw v S {ω | ¬ ∃ k, ω k = none}
          ≤ epochLaw v S {ω | 1 ≤ ∏ k ∈ Finset.range n, nn (ω k)} := by
            apply measure_mono
            intro ω hω
            have hω' : ∀ k, ω k ≠ none := by
              intro k hk; exact hω ⟨k, hk⟩
            show 1 ≤ ∏ k ∈ Finset.range n, nn (ω k)
            rw [Finset.prod_eq_one (fun k _ => by simp [nn, hω' k])]
        _ = 1 * epochLaw v S {ω | 1 ≤ ∏ k ∈ Finset.range n, nn (ω k)} := (one_mul _).symm
        _ ≤ ∫⁻ ω, ∏ k ∈ Finset.range n, nn (ω k) ∂epochLaw v S :=
            mul_meas_ge_le_lintegral hmeas 1
        _ = ∏ k ∈ Finset.range n, ∫⁻ y, nn y ∂choiceMeasure v S :=
            lint_prefix v S hv (fun _ => nn) n
        _ = _ := by rw [Finset.prod_const, Finset.card_range, hb]
    exact le_antisymm
      (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hb1) hle) (by simp)
  have hF_meas : ∀ n, Measurable (F n) := by
    intro n
    apply Measurable.mul
    · exact Finset.measurable_prod _ (fun k _ => hmf f k)
    · exact hmf ind0 n
  have hF_int : ∀ n, ∫⁻ ω, F n ω ∂epochLaw v S =
      (ENNReal.ofReal (∑ o, choiceProb v S o * fr o)) ^ n *
        ENNReal.ofReal (1 / (1 + ∑ j ∈ S, v j)) := by
    intro n
    have hfe : ∀ ω, F n ω =
        ∏ k ∈ Finset.range (n + 1), (if k < n then f else ind0) (ω k) := by
      intro ω
      simp only [F]
      rw [Finset.prod_range_succ]
      congr 1
      · apply Finset.prod_congr rfl
        intro k hk
        simp [Finset.mem_range.1 hk]
      · simp
    simp_rw [hfe]
    rw [lint_prefix v S hv (fun k => if k < n then f else ind0) (n + 1), Finset.prod_range_succ]
    congr 1
    · rw [Finset.prod_congr rfl (g := fun _ => ENNReal.ofReal (∑ o, choiceProb v S o * fr o))
        (fun k hk => by simp [Finset.mem_range.1 hk, ha])]
      simp
    · simp [hq0]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (epochCount i ω : ℝ))) ∂epochLaw v S
      = ∫⁻ ω, ∑' n, F n ω ∂epochLaw v S :=
        lintegral_congr_ae (hnull.mono (fun ω h => claim1 ω h))
    _ = ∑' n, ∫⁻ ω, F n ω ∂epochLaw v S := lintegral_tsum (fun n => (hF_meas n).aemeasurable)
    _ = ∑' n, (ENNReal.ofReal (∑ o, choiceProb v S o * fr o)) ^ n *
          ENNReal.ofReal (1 / (1 + ∑ j ∈ S, v j)) := by simp_rw [hF_int]
    _ = (1 - ENNReal.ofReal (∑ o, choiceProb v S o * fr o))⁻¹ *
          ENNReal.ofReal (1 / (1 + ∑ j ∈ S, v j)) := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (1 / (1 - v i * (Real.exp θ - 1))) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hA0,
          ← ENNReal.ofReal_inv_of_pos (by linarith),
          ← ENNReal.ofReal_mul (inv_nonneg.2 (by linarith))]
        congr 1
        have hD : 0 < 1 - v i * (Real.exp θ - 1) := by linarith
        have h1 : 1 - ((∑ j ∈ S, v j) + v i * (Real.exp θ - 1)) / (1 + ∑ j ∈ S, v j) =
            (1 - v i * (Real.exp θ - 1)) / (1 + ∑ j ∈ S, v j) := by
          field_simp; ring
        rw [hA, h1]
        field_simp
