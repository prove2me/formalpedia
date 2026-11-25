-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_of_pow_mem_of_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:45.213811+00:00
-- url     : https://prove2.me/submissions/7d0c9e18-4c03-4554-9e99-bef86d6f5e26

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
variable {Q Q' : Type*} [Group Q] [Group Q']
namespace GroundTheory.ProfCoh
theorem _root_.solution {S : Subgroup Q} {x : Q} {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a ∈ S) (hb : x ^ b ∈ S) : x ∈ S := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hx : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast x a, ← zpow_natCast x b, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h,
      zpow_one]
  rw [hx]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)
end GroundTheory.ProfCoh
