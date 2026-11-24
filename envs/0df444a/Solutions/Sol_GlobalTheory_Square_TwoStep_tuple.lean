-- Prove2me | solution 1 for GlobalTheory.Square.TwoStep.tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:57:17.064392+00:00
-- url     : https://prove2.me/submissions/43f7624f-84dd-45cd-afcb-ff59eff8c0de

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Theorems.Thm_GlobalTheory_Square_TwoStep_vw_natCast_nonneg
import Theorems.Thm_GlobalTheory_Square_TwoStep_normAlg_coords
import Theorems.Thm_P2M_GlobalTheory_Square_TwoStep_normAlg_coords__aac41224ad99
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
open GlobalTheory.Square.TwoStep
namespace GlobalTheory.Square.TwoStep
theorem _root_.solution (σ₀ : K →+* ℂ) (w : Pl K) {n m Q : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hQ : Q ≠ 0) :
    (square K).Tuple σ₀ (numbers n m Q) (coords K (m * Q)) w (vw w ((2 : ℕ) : K) : ℝ) := by
  have h2 := vw_natCast_nonneg w 2
  have hnat : ∀ (v : Pl K) (t : ℕ), -(vw w ((2 : ℕ) : K) : ℝ) ≤ (vw v (t : K) : ℝ) := fun v t => by
    have := vw_natCast_nonneg v t
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show _ = (∏ _i : Fin 2, (n : ℂ)) * _ * _
    rw [Fin.prod_univ_two]
    simp [square, numbers]; left; ring
  · intro x k; simp [square, numbers, coords]
  · rw [normAlg_coords]
    have : Icc (1 - ((square K).e0 : ℤ)) ((square K).h0 : ℤ) = {0, 1} := by simp only [square]; decide
    rw [this]
    simp [square, numbers]; ring
  · rw [normAlg_coords']; exact one_ne_zero
  · intro s _ _
    simp only [numbers]
    split_ifs <;> simp [hm, hQ]
  · intro i; simp [numbers, hn]
  · intro x; simp [coords]
  · intro x k; exact ⟨hnat _ _, hnat _ _⟩
  · intro x k; exact ⟨by simpa [coords] using hnat w 1, by simpa [coords] using hnat (conjPl w) 1⟩
  · intro x k l
    show _ ≤ (vw w ((1 : K) / ((2 : ℕ) : K)) : ℝ)
    rw [one_div, Formalism.DivisionValues.ValuationRepresentative.vw_inv]; simp
end GlobalTheory.Square.TwoStep
