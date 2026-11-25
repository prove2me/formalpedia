-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_coprime_pow_mem_primaryPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:44.516383+00:00
-- url     : https://prove2.me/submissions/1ac3e9d7-6c53-4bb7-b146-619a1658c5c1

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
    (hx : IsOfFinOrder x) : ∃ m : ℕ, m.Coprime p ∧ x ^ m ∈ primaryPart p Q := by
  obtain ⟨e, m, hm, he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hx.orderOf_pos.ne' p hp.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  refine ⟨m, ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm, Subgroup.subset_closure ⟨e, ?_⟩⟩
  have hdvd : m ∣ orderOf x := ⟨p ^ e, by rw [he, mul_comm]⟩
  rw [orderOf_pow_of_dvd hm0 hdvd, he, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
end GroundTheory.ProfCoh
