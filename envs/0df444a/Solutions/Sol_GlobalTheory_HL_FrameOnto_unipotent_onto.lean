-- Prove2me | solution 1 for GlobalTheory.HL.FrameOnto.unipotent_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:37.268332+00:00
-- url     : https://prove2.me/submissions/448cceed-d00c-42e5-9194-4535687f07ed

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_matrix
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_elt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameOnto
open GlobalTheory.HL.Eichler
namespace GlobalTheory.HL.FrameOnto
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ n ∈ S.N, ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (S.f j) = ∑ i, s i j • S.f i) ∧ (∀ n ∈ S.N', ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (S.f' j) = ∑ i, s i j • S.f' i) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → (∃ n ∈ S.N, ∀ j, n (S.f j) = ∑ i, s i j • S.f i) ∧ ∃ n ∈ S.N', ∀ j, n (S.f' j) = ∑ i, s i j • S.f' i := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  exact ⟨exists_matrix S S.f S.T S.gram, exists_matrix S S.f' S.T' S.gram', fun s hs =>
    ⟨exists_elt S S.f S.es S.T S.gram S.dual s hs, exists_elt S S.f' S.es' S.T' S.gram' S.dual' s hs⟩⟩
end GlobalTheory.HL.FrameOnto
