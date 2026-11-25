-- Prove2me | solution 1 for GlobalTheory.HL.FrameStab.step_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:41:23.574583+00:00
-- url     : https://prove2.me/submissions/260e9366-5201-42b1-ac8d-a20a70cdbbdf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameStab
theorem _root_.solution (g : Fin (r + 1) → S.V)
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1))
    (h : S.GLV) (hg : ∀ j, h (g j) = ∑ i, s i j • g i) (l : ℕ) :
    ∀ v ∈ S.spanTo g (l + 1), h v - v ∈ S.spanTo g l := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' : (j : ℕ) < l + 1 := hj
    rw [hg, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hs.2, one_smul, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun i hi => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · have h' : (i : ℕ) < j := h
      exact Submodule.smul_mem _ _ (mem_spanTo S g (by omega))
    · rw [hs.1 i j h]; simp
  | zero => simp
  | add x y _ _ hx hy =>
    have : h (x + y) - (x + y) = (h x - x) + (h y - y) := by rw [map_add]; abel
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hx
end GlobalTheory.HL.FrameStab
