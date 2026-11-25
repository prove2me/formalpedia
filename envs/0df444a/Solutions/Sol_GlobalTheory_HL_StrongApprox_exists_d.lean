-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.exists_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:13.728291+00:00
-- url     : https://prove2.me/submissions/51e57cba-6dd4-4e95-8ca0-5467e422628f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Theorems.Thm_GlobalTheory_HL_StrongApprox_sig_sig
import Theorems.Thm_GlobalTheory_HL_StrongApprox_sig_ne

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.StrongApprox
theorem _root_.solution (A : Places F E sig) : ∃ d : 𝓞 E, sig (d : E) = -(d : E) ∧ (d : E) ≠ 0 := by
  have hint : ∀ o : 𝓞 E, IsIntegral ℤ (sig (o : E)) := fun o =>
    (o.isIntegral_coe).map (sig.toRingHom.toIntAlgHom)
  suffices h : ∃ o : 𝓞 E, sig (o : E) ≠ o by
    obtain ⟨o, ho⟩ := h
    refine ⟨o - ⟨sig o, hint o⟩, ?_, ?_⟩
    · change sig ((o : E) - sig o) = -((o : E) - sig o)
      rw [map_sub, sig_sig A]; ring
    · change (o : E) - sig o ≠ 0
      rw [sub_ne_zero]
      exact fun h => ho h.symm
  by_contra hne
  push_neg at hne
  obtain ⟨e, he⟩ := sig_ne A
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  apply he
  rw [map_div₀]
  exact congrArg₂ (· / ·) (hne a) (hne s)
end GlobalTheory.HL.StrongApprox
