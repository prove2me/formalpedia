-- Prove2me | solution 1 for GlobalTheory.SW.EisTrans.exists_sub_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:06:19.623225+00:00
-- url     : https://prove2.me/submissions/c1ec1590-6148-4adf-8806-8d1a144842aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisTrans
variable {N : ℕ}
open scoped MatrixOrder
namespace GlobalTheory.SW.EisTrans
theorem _root_.solution {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Y.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ (Y - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨1, one_pos, by rw [Subsingleton.elim (_ - _) 0]; exact PosSemidef.zero⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff (A := Matrix (Fin N) (Fin N) ℂ)
    hY.isStrictlyPositive.isSelfAdjoint).2 fun x hx => hY.isStrictlyPositive.spectrum_pos hx
  refine ⟨r, hr, ?_⟩
  have := Matrix.le_iff.mp hle
  rwa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] at this
end GlobalTheory.SW.EisTrans
