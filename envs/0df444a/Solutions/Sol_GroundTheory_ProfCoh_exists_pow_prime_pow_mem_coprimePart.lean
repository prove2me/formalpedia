-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_pow_prime_pow_mem_coprimePart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:08.437404+00:00
-- url     : https://prove2.me/submissions/c14f4d3b-2710-4f03-8be0-f20dc6897ea4

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) {x : Q}
    (hx : IsOfFinOrder x) : ∃ k : ℕ, x ^ p ^ k ∈ coprimePart p Q := by
  obtain ⟨e, m, hm, he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hx.orderOf_pos.ne' p hp.one_lt.ne'
  refine ⟨e, Subgroup.subset_closure ?_⟩
  have hdvd : p ^ e ∣ orderOf x := ⟨m, he⟩
  rw [Set.mem_ofPred_eq, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, he,
    Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
end GroundTheory.ProfCoh
