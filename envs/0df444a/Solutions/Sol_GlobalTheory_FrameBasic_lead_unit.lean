-- Prove2me | solution 1 for GlobalTheory.FrameBasic.lead_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:03.747373+00:00
-- url     : https://prove2.me/submissions/06a58126-2d81-478b-9d94-94ec1e4d8500

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Theorems.Thm_GlobalTheory_FrameBasic_entry_zero
import Theorems.Thm_GlobalTheory_FrameBasic_entry_unit
import Theorems.Thm_GlobalTheory_FrameBasic_det_mono_unit
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
theorem _root_.solution {n : ℕ} (w : Pt E n) (ε : Fin n → E) (hε : ∀ b, IsUnit (ε b))
    {m : ℕ} (hm : m ≤ n) :
    ((Matrix.of fun a b => w.mat a b * ε b).submatrix (Fin.castLE hm) (Fin.castLE hm)).det ≠ 0 →
    IsUnit ((Matrix.of fun a b => w.mat a b * ε b).submatrix (Fin.castLE hm) (Fin.castLE hm)).det := by
  refine det_mono_unit _ (fun a => if h : sig w.blocks a < m then ⟨_, h⟩ else a) ?_ ?_
  · intro a b hb
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Pt.mat, Fin.val_castLE]
    rw [entry_zero, zero_mul]
    intro h
    apply hb
    rw [dif_pos (h ▸ b.2)]
    exact Fin.ext h
  · intro a
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Pt.mat, Fin.val_castLE]
    split_ifs with h
    · intro _
      exact (entry_unit w.blocks a (by rw [w.size]; omega)).2.mul (hε _)
    · intro h2
      exfalso; apply h2
      rw [entry_zero, zero_mul]
      intro h3
      exact h (h3 ▸ a.2)
end GlobalTheory.FrameBasic
