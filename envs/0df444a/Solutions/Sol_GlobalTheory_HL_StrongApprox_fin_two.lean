-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.fin_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:56:47.808522+00:00
-- url     : https://prove2.me/submissions/748c550e-47d3-4952-b229-b56ca2ea30e6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Theorems.Thm_GlobalTheory_HL_PlacesInt_mem_int_iff


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
theorem _root_.solution (A : Places F E sig) :
    {p : HeightOneSpectrum (𝓞 F) | (A.loc p).ιF 2⁻¹ ∉ 𝒪[(A.loc p).Fp]}.Finite := by
  refine (HeightOneSpectrum.Support.finite (𝓞 F) (2⁻¹ : F)).subset fun p hp => ?_
  have hp' : ¬ (A.loc p).ιF 2⁻¹ ∈ 𝒪[(A.loc p).Fp] := hp
  rw [PlacesInt.mem_int_iff, not_le] at hp'
  exact hp'
end GlobalTheory.HL.StrongApprox
