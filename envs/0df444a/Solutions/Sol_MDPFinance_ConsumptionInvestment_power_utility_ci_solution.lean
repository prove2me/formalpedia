-- Prove2me | solution 1 for MDPFinance.ConsumptionInvestment.power_utility_ci_solution
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:05:29.139013+00:00
-- url     : https://prove2.me/submissions/dac021dc-da61-4824-8ea3-b858bde8b258

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market
import Definitions.Def_MDPFinance_ConsumptionInvestment_PowerAuxiliary

open MeasureTheory ProbabilityTheory MDPFinance.ConsumptionInvestment

namespace CIPowCex

theorem indep_unit {ι : Type} {β : ι → Type} [∀ i, MeasurableSpace (β i)]
    (f : ∀ i, Unit → β i) : iIndepFun f (Measure.dirac ()) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  classical
  by_cases hall : ∀ i ∈ S, f i () ∈ sets i
  · have h1 : () ∈ ⋂ i ∈ S, f i ⁻¹' sets i := by
      simp only [Set.mem_iInter, Set.mem_preimage]; exact hall
    rw [Measure.dirac_apply_of_mem h1]
    symm
    apply Finset.prod_eq_one
    intro i hi
    exact Measure.dirac_apply_of_mem (hall i hi)
  · push_neg at hall
    obtain ⟨j, hj, hjn⟩ := hall
    have h1 : () ∉ ⋂ i ∈ S, f i ⁻¹' sets i := by
      simp only [Set.mem_iInter, Set.mem_preimage, not_forall]; exact ⟨j, hj, hjn⟩
    rw [Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator_of_notMem h1]
    symm
    apply Finset.prod_eq_zero hj
    rw [Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator_of_notMem]
    exact hjn

noncomputable def UU (x : ℝ) : ℝ := x ^ (1 / 2 : ℝ) / (1 / 2)

theorem UU_concave : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) UU := by
  have base := Real.strictConcaveOn_rpow (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have := base.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at this ⊢
  unfold UU
  rw [show a * (x ^ (1 / 2 : ℝ) / (1 / 2)) + b * (y ^ (1 / 2 : ℝ) / (1 / 2)) =
    (a * x ^ (1 / 2 : ℝ) + b * y ^ (1 / 2 : ℝ)) / (1 / 2) by ring]
  exact div_lt_div_of_pos_right this (by norm_num)

theorem UU_mono : StrictMonoOn UU (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  unfold UU
  exact div_lt_div_of_pos_right (Real.rpow_lt_rpow hx hxy (by norm_num)) (by norm_num)

theorem UU_cont : ContinuousOn UU (Set.Ici (0 : ℝ)) := by
  unfold UU
  exact (Continuous.continuousOn (by fun_prop (disch := norm_num)))

noncomputable def M0 : ConsumptionInvestmentMarket Unit 0 where
  measIP := Measure.dirac ()
  isProb := inferInstance
  N := 2
  i := fun n => if n = 1 then -3 / 4 else 3
  hi_pos := fun n h1 h2 => by
    by_cases h : n = 1
    · simp [h]; norm_num
    · simp [h]; norm_num
  R := fun _ _ k => k.elim0
  hR_meas := fun _ _ _ => Measurable.of_discrete
  hR_indep := indep_unit _
  hNA := fun _ _ _ => by
    rintro ⟨a, _, hpos⟩
    simp at hpos
  domU := Set.Ici 0
  Uc := UU
  Up := UU
  hUc_mono := UU_mono
  hUc_concave := UU_concave
  hUc_cont := UU_cont
  hUp_mono := UU_mono
  hUp_concave := UU_concave
  hUp_cont := UU_cont

theorem vPower_one (n : ℕ) : M0.vPower (1 / 2) n = 1 := by
  unfold ConsumptionInvestmentMarket.vPower
  have hmem : ∀ α : Fin 0 → ℝ, α ∈ M0.Afrac n :=
    fun α => show ∀ᵐ ω ∂M0.measIP, 0 ≤ 1 + ∑ k, α k * M0.R (n + 1) ω k from
      Filter.Eventually.of_forall fun ω => by simp
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Real.one_rpow, integral_const,
    smul_eq_mul, mul_one]
  rw [ciSup_unique]
  rw [ciSup_pos (hmem _)]
  simp [M0]

end CIPowCex

open CIPowCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hFM2 : M.FM2) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdomU : M.domU = Set.Ici (0 : ℝ)) (hUc : ∀ x ≥ (0 : ℝ), M.Uc x = x ^ γ / γ)
    (hUp : ∀ x ≥ (0 : ℝ), M.Up x = x ^ γ / γ)
    (dseq : ℕ → ℝ) (hdpos : ∀ n ≤ M.N, 0 < dseq n) (hdN : dseq M.N = 1 / γ)
    (hdrec : ∀ n < M.N,
      dseq n ^ ((1 - γ)⁻¹) = γ ^ (-(1 - γ)⁻¹) +
        ((1 + M.i (n + 1)) ^ γ * M.vPower γ n) ^ ((1 - γ)⁻¹) * dseq (n + 1) ^ ((1 - γ)⁻¹)),
    (∀ n ≤ M.N, ∀ x ≥ (0 : ℝ), M.V n x = ((dseq n * x ^ γ : ℝ) : EReal)) ∧
      (∀ n < M.N, dseq (n + 1) ≤ dseq n) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.Afrac n ∧
          ∫ ω, (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ^ γ ∂M.measIP = M.vPower γ n) ∧
        ∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x ≥ (0 : ℝ), (fstar n x).1 = x * (γ * dseq n) ^ (-(1 - γ)⁻¹)) ∧
          (∀ n < M.N, ∀ x ≥ (0 : ℝ), (fstar n x).2 =
            fun k => x * (((γ * dseq n) ^ (1 - γ)⁻¹ - 1) / (γ * dseq n) ^ (1 - γ)⁻¹) *
              αstar n k) ∧
          ∀ x ≥ (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x)) := by
  intro h
  let dseq : ℕ → ℝ := fun n => if n = 0 then 3 else if n = 1 then Real.sqrt 20 else 2
  have hs20 : (0 : ℝ) < Real.sqrt 20 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 20 ^ 2 = 20 := Real.sq_sqrt (by norm_num)
  have e2 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
  have hrec : ∀ n < M0.N,
      dseq n ^ ((1 - (1 / 2 : ℝ))⁻¹) = (1 / 2 : ℝ) ^ (-(1 - (1 / 2 : ℝ))⁻¹) +
        ((1 + M0.i (n + 1)) ^ (1 / 2 : ℝ) * M0.vPower (1 / 2) n) ^ ((1 - (1 / 2 : ℝ))⁻¹) *
          dseq (n + 1) ^ ((1 - (1 / 2 : ℝ))⁻¹) := by
    intro n hn
    rw [e2, vPower_one, mul_one, Real.rpow_neg (by norm_num)]
    simp only [Real.rpow_two]
    have hi : 0 ≤ 1 + M0.i (n + 1) := by
      show 0 ≤ 1 + (if n + 1 = 1 then (-3 / 4 : ℝ) else 3)
      split_ifs <;> norm_num
    rw [← Real.rpow_natCast ((1 + M0.i (n + 1)) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hi]
    norm_num
    have : n = 0 ∨ n = 1 := by
      have : n < 2 := hn
      omega
    rcases this with rfl | rfl
    · simp [dseq, M0, hsq]; norm_num
    · simp [dseq, M0, hsq]; norm_num
  have H := (h M0 (fun _ _ _ => by simp) (1 / 2) (by norm_num) (by norm_num) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) dseq
    (fun n _ => by simp only [dseq]; split_ifs <;> positivity)
    (by show dseq 2 = 1 / (1 / 2); simp [dseq]) hrec).2.1 0 (by show 0 < 2; norm_num)
  simp only [dseq] at H
  norm_num at H
  have : Real.sqrt 20 ≤ Real.sqrt 9 := by
    rw [show Real.sqrt 9 = 3 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact H
  have := Real.sqrt_le_sqrt_iff (by norm_num : (0 : ℝ) ≤ 9) |>.mp this
  norm_num at this

#print axioms solution
