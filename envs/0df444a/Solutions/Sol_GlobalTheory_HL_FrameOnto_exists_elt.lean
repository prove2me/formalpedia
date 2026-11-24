-- Prove2me | solution 1 for GlobalTheory.HL.FrameOnto.exists_elt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:26:03.685413+00:00
-- url     : https://prove2.me/submissions/35dd0b0f-72c4-48f1-b3cd-5deebd6604be

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_upto
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameOnto
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
include gram dual
namespace GlobalTheory.HL.FrameOnto
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F]
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) :
    ∃ n ∈ S.Nof g, ∀ j, n (g j) = ∑ i, s i j • g i := by
  have hx : ∀ j : Fin (r + 1), ∑ i ∈ Finset.univ.erase j, s i j • g i ∈ S.spanTo g j := by
    intro j
    refine Submodule.sum_mem _ fun i hi => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · exact Submodule.smul_mem _ _ (mem_spanTo S g h)
    · rw [hs.1 i j h]; simp
  obtain ⟨n, hn, h⟩ := exists_upto S g gs T gram dual _ hx (r + 1)
  refine ⟨n, hn, fun j => ?_⟩
  rw [h, if_pos j.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hs.2, one_smul]
end GlobalTheory.HL.FrameOnto
