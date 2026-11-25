-- Prove2me | solution 1 for GlobalTheory.SW.SwdAut.transl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:27.830822+00:00
-- url     : https://prove2.me/submissions/e82f0757-ce45-4ca9-b94a-dbf4c51cca4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearity
import Theorems.Thm_GlobalTheory_SW_Base_ccT_one
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_one
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SwdAut
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
namespace GlobalTheory.SW.SwdAut
theorem _root_.solution {β : Matrix (Fin N) (Fin N) E} (hβ : ccT β = β) :
    (fromBlocks 1 β 0 1 : M2 E N) ∈ UU E N := by
  have h : ccT (fromBlocks 1 β 0 1 : M2 E N) = fromBlocks 1 0 β 1 := by
    have h1 := Base.ccT_one (E := E) (α := Fin N)
    ext (i | i) (j | j)
    · exact congrFun (congrFun h1 i) j
    · simp [ccT, cc]
    · exact congrFun (congrFun hβ i) j
    · exact congrFun (congrFun h1 i) j
  change ccT _ * _ * _ = _
  rw [h, Matrix.J, fromBlocks_multiply, fromBlocks_multiply]
  simp
end GlobalTheory.SW.SwdAut
