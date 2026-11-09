-- Prove2me | solution 1 for NonstatNV.observation_1a
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:18:13.547452+00:00
-- url     : https://prove2.me/submissions/094c67ed-6d9a-44f9-a834-016368c2129f

import Definitions.Def_NonstatNV_Model_Standing
import Definitions.Def_NonstatNV_Model_LipschitzCost
import Definitions.Def_NonstatNV_Model_IsArgminSelection
import Definitions.Def_NonstatNV_Model_IsInstance
import Definitions.Def_NonstatNV_demandVariation
import Definitions.Def_NonstatNV_Model_intervalRegret
import Definitions.Def_NonstatNV_Model_predictionPolicy

open MeasureTheory

open NonstatNV in
theorem solution (M : Model) (ℓ : ℝ) (hM : M.Standing) (hℓ : M.LipschitzCost ℓ)
    (sel : ℝ → ℝ → ℝ → ℝ) (hsel : M.IsArgminSelection sel)
    (T : ℕ) (v α : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (μ b h a : ℕ → ℝ) (hinst : M.IsInstance T μ b h)
    (hV : demandVariation μ T ≤ (T : ℝ) ^ v)
    (hpred : ∑ t ∈ Finset.Icc 1 T, |a t - μ t| ≤ (T : ℝ) ^ α) :
    M.intervalRegret μ b h (M.predictionPolicy sel b h a) 1 T ≤ 2 * ℓ * (T : ℝ) ^ α := by
  have hmm : M.μmin ≤ M.μmax := hM.1
  haveI : Nonempty M.Q := hM.2.2.2.1.to_subtype
  have hcl : ∀ x μ0, μ0 ∈ Set.Icc M.μmin M.μmax → |M.clamp x - μ0| ≤ |x - μ0| := by
    intro x μ0 hμ0
    unfold Model.clamp
    rcases le_total x M.μmax with h1 | h1
    · rw [min_eq_right h1]
      rcases le_total M.μmin x with h2 | h2
      · rw [max_eq_right h2]
      · rw [max_eq_left h2, abs_of_nonpos (by linarith [hμ0.1]),
          abs_of_nonpos (by linarith [hμ0.1])]
        linarith
    · rw [min_eq_left h1, max_eq_right hmm, abs_of_nonneg (by linarith [hμ0.2]),
        abs_of_nonneg (by linarith [hμ0.2])]
      linarith
  have hclmem : ∀ x, M.clamp x ∈ Set.Icc M.μmin M.μmax := fun x =>
    ⟨le_max_left _ _, max_le hmm (min_le_left _ _)⟩
  have hconst : M.intervalRegret μ b h (M.predictionPolicy sel b h a) 1 T =
      ∑ t ∈ Finset.Icc 1 T, (M.cost (μ t) (b t) (h t) (sel (M.clamp (a t)) (b t) (h t)) -
        M.opt (μ t) (b t) (h t)) := by
    unfold Model.intervalRegret Model.predictionPolicy Model.demandLaw
    rw [integral_const]
    simp
  rw [hconst]
  have hterm : ∀ t ∈ Finset.Icc 1 T,
      M.cost (μ t) (b t) (h t) (sel (M.clamp (a t)) (b t) (h t)) - M.opt (μ t) (b t) (h t) ≤
        2 * ℓ * |a t - μ t| := by
    intro t ht
    obtain ⟨hμt, hbt, hht⟩ := hinst t ht
    obtain ⟨hq1, hmin1⟩ := hsel.1 (M.clamp (a t)) (hclmem _) (b t) hbt (h t) hht
    obtain ⟨hq2, hmin2⟩ := hsel.1 (μ t) hμt (b t) hbt (h t) hht
    have hopt : M.cost (μ t) (b t) (h t) (sel (μ t) (b t) (h t)) ≤ M.opt (μ t) (b t) (h t) := by
      unfold Model.opt
      exact le_ciInf fun q => hmin2 q q.2
    have L1 := hℓ.2 (b t) hbt (h t) hht _ hq1 (μ t) hμt (M.clamp (a t)) (hclmem _)
    have L2 := hℓ.2 (b t) hbt (h t) hht _ hq2 (M.clamp (a t)) (hclmem _) (μ t) hμt
    have m1 := hmin1 _ hq2
    have hc := hcl (a t) (μ t) hμt
    rw [abs_sub_comm (M.clamp (a t)) (μ t)] at hc
    have e1 := le_abs_self (M.cost (μ t) (b t) (h t) (sel (M.clamp (a t)) (b t) (h t)) -
      M.cost (M.clamp (a t)) (b t) (h t) (sel (M.clamp (a t)) (b t) (h t)))
    have e2 := le_abs_self (M.cost (M.clamp (a t)) (b t) (h t) (sel (μ t) (b t) (h t)) -
      M.cost (μ t) (b t) (h t) (sel (μ t) (b t) (h t)))
    rw [abs_sub_comm (M.clamp (a t)) (μ t)] at L2
    have hl := hℓ.1
    have h3 : ℓ * |μ t - M.clamp (a t)| ≤ ℓ * |a t - μ t| := mul_le_mul_of_nonneg_left hc hl
    linarith
  calc _ ≤ ∑ t ∈ Finset.Icc 1 T, 2 * ℓ * |a t - μ t| := Finset.sum_le_sum hterm
    _ = 2 * ℓ * ∑ t ∈ Finset.Icc 1 T, |a t - μ t| := by rw [Finset.mul_sum]
    _ ≤ 2 * ℓ * (T : ℝ) ^ α := mul_le_mul_of_nonneg_left hpred (by linarith [hℓ.1])
