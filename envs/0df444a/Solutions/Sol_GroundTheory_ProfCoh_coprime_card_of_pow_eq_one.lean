-- Prove2me | solution 1 for GroundTheory.ProfCoh.coprime_card_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:06.865435+00:00
-- url     : https://prove2.me/submissions/c2d88bad-d44e-4e80-90f3-c23c85a5b889

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
theorem _root_.solution {p : ℕ} [Fact p.Prime] [Finite Q]
    (h : ∀ x : Q, x ^ p = 1 → x = 1) : (Nat.card Q).Coprime p := by
  refine ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun hdvd ↦ ?_).symm
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 := h x (hx ▸ pow_orderOf_eq_one x)
  rw [h1, orderOf_one] at hx
  exact (Fact.out : p.Prime).one_lt.ne hx
end GroundTheory.ProfCoh
