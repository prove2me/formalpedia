-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:13:28.424975+00:00
-- url     : https://prove2.me/submissions/cfbc0d71-76f3-4740-96e2-d028fe1e66cb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Theorems.Thm_GlobalTheory_HL_StrongApprox_int_of
import Theorems.Thm_GlobalTheory_HL_StrongApprox_small_local
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.HL.StrongApprox
theorem _root_.solution (A : Places F E sig) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (w : ∀ p, (A.loc p).Fp) (hw : ∀ p ∈ S, w p ≠ 0) :
    ∃ h : 𝓞 F, h ≠ 0 ∧ ∀ p ∈ S,
      valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F h)) ≤ valuation (A.loc p).Fp (w p) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert q S hq ih =>
    obtain ⟨h, hh, hS⟩ := ih (fun p hp => hw p (Finset.mem_insert_of_mem hp))
    obtain ⟨a, ha, ha'⟩ := small_local (A.loc q) (w q) (hw q (Finset.mem_insert_self q S))
    refine ⟨h * a, mul_ne_zero hh ha, fun p hp => ?_⟩
    rw [map_mul, map_mul, Valuation.map_mul]
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact (mul_le_of_le_one_left' (int_of _ h)).trans ha'
    · exact (mul_le_of_le_one_right' (int_of _ a)).trans (hS p hp)
end GlobalTheory.HL.StrongApprox
