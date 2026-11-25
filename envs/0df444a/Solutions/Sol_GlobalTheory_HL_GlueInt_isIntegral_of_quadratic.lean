-- Prove2me | solution 1 for GlobalTheory.HL.GlueInt.isIntegral_of_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:42:10.689569+00:00
-- url     : https://prove2.me/submissions/82f6e264-293e-469a-9c8e-7b9d84157a68

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfIntegralAllQuadraticCompletions
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlueInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.GlueInt
theorem _root_.solution (y a b : E) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (h : y ^ 2 - a * y + b = 0) : IsIntegral ℤ y := by
  have hR : IsIntegral (integralClosure ℤ E) y := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨a, ha⟩ : integralClosure ℤ E) * Polynomial.X +
      Polynomial.C (⟨b, hb⟩ : integralClosure ℤ E), by monicity!, ?_⟩
    simpa [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul] using h
  exact isIntegral_trans y hR
end GlobalTheory.HL.GlueInt
