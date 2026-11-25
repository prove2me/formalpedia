-- Prove2me | solution 1 for GlobalTheory.CubeLift.eq_one_of_del
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:58:01.132598+00:00
-- url     : https://prove2.me/submissions/02892c97-7c4a-418a-934e-866f297bd94f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_add_unique
import Theorems.Thm_P2M_GlobalTheory_CubeLift_mem_cong__73390d79565c
import Theorems.Thm_GlobalTheory_CubeLift_lin_del
import Theorems.Thm_GlobalTheory_CubeLift_um_tri_del
import Theorems.Thm_GlobalTheory_CubeLift_cong_mono
import Theorems.Thm_GlobalTheory_CubeLift_exists_cong_pow
import Theorems.Thm_GlobalTheory_CubeLift_pow_mul_pow_le

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
theorem _root_.solution {g : (A[X])ˣ} {J : Ideal A} (hJ : IsNilpotent J) (h : g ∈ cong J)
    (hg : del g p₁ p₂ p₃ = 1) : g = 1 := by
  have ind : ∀ k : ℕ, g ∈ cong (J ^ (k + 1)) := fun k => by
    induction k with
    | zero => rwa [zero_add, pow_one]
    | succ k ih =>
      refine cong_mono (pow_mul_pow_le J k) (mem_cong'.2 (add_unique (lin _ g) fun Y _ a b c => ?_))
      rw [← lin_del ih, ← um_tri_del, hg, map_one, lin, Units.val_one, sub_self, map_zero]
  obtain ⟨n, hn⟩ := exists_cong_pow (X := X) hJ
  exact hn g (ind n)
end GlobalTheory.CubeLift
