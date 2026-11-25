-- Prove2me | solution 1 for GlobalTheory.SW.SwdAut.classSum_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:17:43.892896+00:00
-- url     : https://prove2.me/submissions/730834a0-05e7-445b-b275-2b4a40edda77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearity
import Theorems.Thm_GlobalTheory_SW_finite_cls_and_stab
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
theorem _root_.solution {M : ℕ} (hM : 0 < M) (f g : Lt E n → ℂ) :
    classSum M (fun Λ => f Λ + g Λ) = classSum M f + classSum M g := by
  haveI := (finite_cls_and_stab E n M hM).1
  haveI := Fintype.ofFinite (Cls E n M)
  simp only [classSum, finsum_eq_sum_of_fintype, mul_add, Finset.sum_add_distrib]
end GlobalTheory.SW.SwdAut
