-- Prove2me | solution 1 for GlobalTheory.CubeLift.isNilpotent_of_rd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:02:33.850355+00:00
-- url     : https://prove2.me/submissions/ea68fec3-4492-4ddd-97c4-98637d1656aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_rd_eq_zero
import Theorems.Thm_GlobalTheory_CubeLift_rd_mul
import Theorems.Thm_GlobalTheory_CubeLift_rd_mono
import Theorems.Thm_GlobalTheory_CubeLift_eq_zero_of_rd

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
theorem _root_.solution {I : Ideal A} (hI : IsNilpotent I) {u : A[X]} (hu : rd I u = 0) : IsNilpotent u := by
  obtain ⟨n, hn⟩ := hI
  have : ∀ k : ℕ, rd (I ^ k) (u ^ k) = 0 := fun k => by
    induction k with
    | zero => exact rd_eq_zero.2 fun x => by simp
    | succ k ih => rw [pow_succ, pow_succ]; exact rd_mul ih hu
  exact ⟨n, eq_zero_of_rd (rd_mono hn.le (this n))⟩
end GlobalTheory.CubeLift
