-- Prove2me | solution 1 for GlobalTheory.SW.theta_eis_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:03.320103+00:00
-- url     : https://prove2.me/submissions/a82bdabc-860a-4959-b4e7-dba72ea3234f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBounded
import Theorems.Thm_GlobalTheory_SW_EisBdd_theta_bdd
import Theorems.Thm_GlobalTheory_SW_EisBdd_eis_bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.EisBdd
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (R : ℕ) (δ : ℝ), 0 < R → 0 < δ → ∃ C : ℝ, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, HasLevel R φ → ∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → ∀ Z ∈ HnGe Ψ N δ, (Summable fun U : Lag E N => ‖eisTerm Ψ U.2.choose φ Z 0 0‖) ∧ ‖thH Ψ φ Z 0 0‖ ≤ C * B ∧ ‖eis Ψ φ Z 0 0‖ ≤ C * B := by
  intro E _ _ _ Ψ hΨ n N hn hN R δ hR hδ
  obtain ⟨C₁, h₁⟩ := theta_bdd (n := n) (N := N) hΨ hR hδ
  obtain ⟨C₂, h₂⟩ := eis_bdd hΨ hn hN hR hδ
  refine ⟨max C₁ C₂, fun φ hφ B hB Z hZ => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  exact ⟨(h₂ φ hφ B hB Z hZ).1,
    (h₁ φ hφ B hB Z hZ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB0),
    (h₂ φ hφ B hB Z hZ).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hB0)⟩
end GlobalTheory.SW
