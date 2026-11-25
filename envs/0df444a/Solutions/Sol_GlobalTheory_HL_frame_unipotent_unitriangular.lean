-- Prove2me | solution 1 for GlobalTheory.HL.frame_unipotent_unitriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:34.310807+00:00
-- url     : https://prove2.me/submissions/2b78f9a7-dece-457c-a2de-38fc67456163

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Theorems.Thm_GlobalTheory_HL_FrameTri_linInd
import Theorems.Thm_GlobalTheory_HL_FrameTri_map_mem_iff
import Theorems.Thm_GlobalTheory_HL_FrameTri_spanTo_comp
import Theorems.Thm_GlobalTheory_HL_FrameTri_exists_tri

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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → LinearIndependent E g ∧ ∀ n ∈ S.Nof g, (∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (g j) = ∑ i, s i j • g i) ∧ (∀ j, S.spanTo (fun b => n (g b)) j = S.spanTo g j) ∧ (∀ j, ∀ v, n v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j) ∧ ∀ v, n v ∈ perp L S.Hm (S.spanTo g r) ↔ v ∈ perp L S.Hm (S.spanTo g r) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs h
  obtain ⟨t, hg, hd⟩ : ∃ t : Fˣ, (∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t else 0) ∧
      ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0 := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨S.T, S.gram, S.dual⟩
    · exact ⟨S.T', S.gram', S.dual'⟩
  exact ⟨FrameTri.linInd S g gs t hg hd, fun n hn => ⟨FrameTri.exists_tri S g t hg hn,
    FrameTri.spanTo_comp S g t hg hn, FrameTri.map_mem_iff S g t hg hn, hn.2.1⟩⟩
end GlobalTheory.HL
