-- Prove2me | solution 1 for GlobalTheory.SW.Reduct.den_smul_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:33.207209+00:00
-- url     : https://prove2.me/submissions/e42fc2a6-1e88-4965-be02-e39505776966

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Reduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.SW.Reduct
theorem _root_.solution {N D : ℕ} {t : E} (h : IsIntegral ℤ ((D : E) * t)) :
    Den D (t • Matrix.J (Fin N) E) := by
  rintro (i | i) (j | j) <;> by_cases hij : i = j <;>
    simp [Matrix.J, Matrix.one_apply, hij, isIntegral_zero, h, h.neg]
end GlobalTheory.SW.Reduct
