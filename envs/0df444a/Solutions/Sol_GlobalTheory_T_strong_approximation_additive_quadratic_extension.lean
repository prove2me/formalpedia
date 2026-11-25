-- Prove2me | solution 1 for GlobalTheory.T.strong_approximation_additive_quadratic_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:36.825242+00:00
-- url     : https://prove2.me/submissions/31961a07-dec5-4ac0-a126-8b6fe3f2ec0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtensionStatement
import Theorems.Thm_GlobalTheory_HL_StrongApprox_strong_approx_additive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → (∀ y : ∀ p, (A.loc p).Fp, {p | y p ∉ 𝒪[(A.loc p).Fp]}.Finite → ∃ x : F, ∀ p, ∃ o : 𝒪[(A.loc p).Fp], (A.loc p).ιF x - y p = c p * o) ∧ (∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite → ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o) ∧ ∀ (t : E) (y : ∀ p, (A.loc p).Ep), {p | y p ∉ (A.L p).O}.Finite → (∀ p, y p + (A.L p).cj (y p) = (A.loc p).ιE t) → ∃ x : E, x + sig x = t ∧ ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  first | exact @GlobalTheory.HL.StrongApprox.strong_approx_additive | exact GlobalTheory.HL.StrongApprox.strong_approx_additive | (intros; apply GlobalTheory.HL.StrongApprox.strong_approx_additive <;> assumption)
end _root_.GlobalTheory.T
