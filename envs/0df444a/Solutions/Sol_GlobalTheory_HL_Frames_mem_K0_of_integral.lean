-- Prove2me | solution 1 for GlobalTheory.HL.Frames.mem_K0_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:58:15.468633+00:00
-- url     : https://prove2.me/submissions/c9757d22-968d-47ee-8b95-8f566fee4b11

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemMaximalCompactOfIntegral
import Theorems.Thm_GlobalTheory_HL_Frames_stab_span_of_integral

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Frames
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Frames
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (h : S.GLV) (s si s' si' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), h ∈ S.St → (∀ i j, s i j ∈ L.O) → (∀ i j, si i j ∈ L.O) → s * si = 1 → (∀ i j, s' i j ∈ L.O) → (∀ i j, si' i j ∈ L.O) → s' * si' = 1 → (∀ j, h (S.f j) = ∑ i, s i j • S.f i) → (∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) → h ∈ S.K0 := by
  intro F _ _ _ E _ _ _ L r k S h s si s' si' hSt hs hsi hm hs' hsi' hm' hg hg'
  unfold Frames.K0
  exact ⟨⟨hSt, S.stab_span_of_integral h S.f s si hs hsi hm hg⟩,
    S.stab_span_of_integral h S.f' s' si' hs' hsi' hm' hg'⟩
end GlobalTheory.HL.Frames
