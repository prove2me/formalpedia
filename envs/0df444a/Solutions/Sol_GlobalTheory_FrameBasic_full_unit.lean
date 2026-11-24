-- Prove2me | solution 1 for GlobalTheory.FrameBasic.full_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:02.675895+00:00
-- url     : https://prove2.me/submissions/fc4de73c-5c8a-46a3-85f1-8b9fa3c2388b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Theorems.Thm_GlobalTheory_FrameBasic_sig_sig
import Theorems.Thm_GlobalTheory_FrameBasic_entry_zero
import Theorems.Thm_GlobalTheory_FrameBasic_entry_unit
import Theorems.Thm_GlobalTheory_FrameBasic_det_mono
import Theorems.Thm_GlobalTheory_FrameBasic_det_perm_unit
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]
namespace GlobalTheory.FrameBasic
theorem _root_.solution {n : ℕ} (w : Pt E n) (ε : Fin n → E) (hε : ∀ b, IsUnit (ε b)) :
    IsUnit (Matrix.of fun a b => w.mat a b * ε b).det := by
  have hs : ∀ a : Fin n, sig w.blocks a < n := fun a => by
    have := (entry_unit w.blocks a (by rw [w.size]; omega)).1
    rwa [w.size] at this
  rw [det_mono _ (fun a => ⟨_, hs a⟩)]
  · refine IsUnit.mul ?_ (det_perm_unit _ ?_)
    · rw [IsUnit.prod_univ_iff]
      intro a
      exact (entry_unit w.blocks a (by rw [w.size]; omega)).2.mul (hε _)
    · intro a b hab
      have h1 : sig w.blocks a = sig w.blocks b := congrArg Fin.val hab
      apply Fin.ext
      rw [← sig_sig w.blocks a, h1, sig_sig]
  · intro a b hb
    simp only [Matrix.of_apply, Pt.mat]
    rw [entry_zero, zero_mul]
    intro h
    exact hb (Fin.ext h)
end GlobalTheory.FrameBasic
