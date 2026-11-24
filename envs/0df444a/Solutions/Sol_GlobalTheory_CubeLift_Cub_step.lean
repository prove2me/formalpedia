-- Prove2me | solution 1 for GlobalTheory.CubeLift.Cub.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:40:58.631998+00:00
-- url     : https://prove2.me/submissions/1d4d148c-3c3f-4caa-874a-be9b196b3f0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_mv_id
import Theorems.Thm_GlobalTheory_CubeLift_add_exists
import Theorems.Thm_GlobalTheory_CubeLift_rd_avg
import Theorems.Thm_GlobalTheory_CubeLift_isNilpotent_of_rd
import Theorems.Thm_P2M_GlobalTheory_CubeLift_mem_cong__73390d79565c
import Theorems.Thm_GlobalTheory_CubeLift_um_mem
import Theorems.Thm_GlobalTheory_CubeLift_lin_mul
import Theorems.Thm_GlobalTheory_CubeLift_lin_div
import Theorems.Thm_GlobalTheory_CubeLift_lin_um
import Theorems.Thm_GlobalTheory_CubeLift_del_mem
import Theorems.Thm_GlobalTheory_CubeLift_lin_del
import Theorems.Thm_GlobalTheory_CubeLift_tri_p

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
namespace Cub
theorem _root_.solution {e : (A[X × X × X])ˣ} (he : Cub e) {I : Ideal A} (hI : IsNilpotent I) (h : e ∈ cong I) :
    ∃ g ∈ cong I, e / del g p₁ p₂ p₃ ∈ cong (I * I) := by
  have h₀ : rd I (avg (avg (e.val - 1))) = 0 := by rw [rd_avg, rd_avg, mem_cong'.1 h, map_zero, map_zero]
  obtain ⟨g, hg⟩ := (isNilpotent_of_rd hI h₀).isUnit_add_one
  have hg' : g ∈ cong I := mem_cong'.2 (by rw [hg, add_sub_cancel_right, h₀])
  have lg : lin I g = avg (avg (lin I e)) := by rw [lin, lin, hg, add_sub_cancel_right, rd_avg, rd_avg]
  refine ⟨g, hg', mem_cong'.2 ?_⟩
  have := add_exists (lin I e) (fun Y _ a b c => by rw [← lin_um, ← lin_um, he.s₁])
    (fun Y _ a b c => by rw [← lin_um, ← lin_um, he.s₂]) (fun Y _ a b c d => by
      simp only [← lin_um]
      rw [← lin_mul (um_mem _ h) (um_mem _ h), he.co, lin_mul (um_mem _ h) (um_mem _ h)]) p₁ p₂ p₃
  rw [tri_p, mv_id, ← lg, ← lin_del hg'] at this
  exact (lin_div h (del_mem hg' _ _ _)).trans (sub_eq_zero.2 this)
end Cub
end GlobalTheory.CubeLift
