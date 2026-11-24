-- Prove2me | solution 1 for GlobalTheory.HL.CoordExist.hf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:06:33.885246+00:00
-- url     : https://prove2.me/submissions/c1009972-5927-47fb-b3d3-f982920a3af2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Theorems.Thm_GlobalTheory_HL_CoordExist_h_sum_left
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordExist
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HL.CoordExist
theorem _root_.solution (H : HermSp M V) {n : ℕ} (b : Fin n → V) (c d : Fin n → E) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) c d = H.h (∑ i, c i • b i) (∑ j, d j • b j) := by

  have hr : ∀ (x : V) (d : Fin n → E), H.h x (∑ j, d j • b j) = ∑ j, M.L.cj (d j) * H.h x (b j) := by
    intro x d
    rw [H.h_herm, h_sum_left, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← H.h_herm]
  rw [h_sum_left]
  unfold GlobalTheory.HL.hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  ring
end GlobalTheory.HL.CoordExist
