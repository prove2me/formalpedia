-- Prove2me | solution 1 for GlobalTheory.CubeLift.Cub.exists_del
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:50.3102+00:00
-- url     : https://prove2.me/submissions/c65e27ed-5117-49e4-b8a4-0f00d66acf1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_del_mul
import Theorems.Thm_GlobalTheory_CubeLift_Cub_div_del
import Theorems.Thm_GlobalTheory_CubeLift_Cub_step
import Theorems.Thm_GlobalTheory_CubeLift_cong_mono
import Theorems.Thm_GlobalTheory_CubeLift_exists_cong_pow
import Theorems.Thm_GlobalTheory_CubeLift_pow_mul_pow_le
import Theorems.Thm_GlobalTheory_CubeLift_del_one

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
theorem _root_.solution {e : (A[X × X × X])ˣ} (he : Cub e) {J : Ideal A} (hJ : IsNilpotent J) (h : e ∈ cong J) :
    ∃ g ∈ cong J, e = del g p₁ p₂ p₃ := by
  have ind : ∀ k : ℕ, ∃ g ∈ cong J, e / del g p₁ p₂ p₃ ∈ cong (J ^ (k + 1)) := fun k => by
    induction k with
    | zero => exact ⟨1, one_mem _, by rwa [del_one, div_one, zero_add, pow_one]⟩
    | succ k ih =>
      obtain ⟨g, hg, hu⟩ := ih
      obtain ⟨g', hg', hu'⟩ := (he.div_del g).step (hJ.pow_succ k) hu
      refine ⟨g * g', mul_mem hg (cong_mono (Ideal.pow_le_self (by omega)) hg'), ?_⟩
      rw [del_mul, ← div_div]
      exact cong_mono (pow_mul_pow_le J k) hu'
  obtain ⟨n, hn⟩ := exists_cong_pow (X := X × X × X) hJ
  obtain ⟨g, hg, e⟩ := ind n
  exact ⟨g, hg, div_eq_one.1 (hn _ e)⟩
end Cub
end GlobalTheory.CubeLift
