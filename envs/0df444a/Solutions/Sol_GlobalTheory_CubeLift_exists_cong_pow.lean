-- Prove2me | solution 1 for GlobalTheory.CubeLift.exists_cong_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:42.121097+00:00
-- url     : https://prove2.me/submissions/ed8cf611-f2d0-4652-a3b3-b6a79a02a486

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_eq_zero_of_rd
import Theorems.Thm_P2M_GlobalTheory_CubeLift_mem_cong__73390d79565c
import Theorems.Thm_GlobalTheory_CubeLift_cong_mono

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
theorem _root_.solution {J : Ideal A} (hJ : IsNilpotent J) :
    ∃ n : ℕ, ∀ u : (A[X])ˣ, u ∈ cong (J ^ (n + 1)) → u = 1 := by
  obtain ⟨n, hn⟩ := hJ
  have : J ^ (n + 1) ≤ ⊥ := by rw [pow_succ, hn]; simp
  exact ⟨n, fun u hu => Units.ext (sub_eq_zero.1 (eq_zero_of_rd (mem_cong'.1 (cong_mono this hu))))⟩
end GlobalTheory.CubeLift
