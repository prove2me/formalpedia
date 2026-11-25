-- Prove2me | solution 1 for GlobalTheory.CechDR.sgn_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:29:14.469818+00:00
-- url     : https://prove2.me/submissions/4c2f631a-d0ee-4b76-9349-14ab36a1f4e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap

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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B}
namespace GlobalTheory.CechDR
theorem _root_.solution {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^j Ω[B⁄R]) : sgn x = (-1) ^ j * x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap b => simp
  | add x y i _ _ hx hy => rw [map_add, hx, hy, mul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    rw [map_mul, sgn_ι, ih, pow_succ]
    rcases neg_one_pow_eq_or (DR R B) i with h | h <;> simp [h]
end GlobalTheory.CechDR
