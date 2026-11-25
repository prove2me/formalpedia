-- Prove2me | solution 1 for GlobalTheory.SW.TwistBound.diag_mem_UU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:33.208141+00:00
-- url     : https://prove2.me/submissions/bff8dcb6-8b12-4f67-83a4-cb0c97f9469f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceInvariantNormBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalMatrixMoveAdmissibleUniformLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistedSiegelWeilDifferenceBounded
import Theorems.Thm_GlobalTheory_SW_Base_ccT_ccT
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul
import Theorems.Thm_GlobalTheory_SW_Base_ccT_one
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_ccT
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_mul
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_one
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_ccT_mul
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_ccT_one
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.TwistBound
theorem _root_.solution {a d : Matrix (Fin N) (Fin N) E} (h : ccT a * d = 1) :
    Matrix.fromBlocks a 0 0 d ∈ UU E N := by
  have h' : ccT d * a = 1 := by
    have := congrArg ccT h
    rwa [Base.ccT_mul, Base.ccT_ccT, Base.ccT_one] at this
  have e : ccT (Matrix.fromBlocks a 0 0 d : M2 E N) = Matrix.fromBlocks (ccT a) 0 0 (ccT d) := by
    ext (i | i) (j | j) <;> simp [ccT, cc]
  change ccT _ * _ * _ = _
  rw [e, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [h, h']
end GlobalTheory.SW.TwistBound
