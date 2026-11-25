-- Prove2me | solution 1 for GroundTheory.GroupCoh.range_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:44.935763+00:00
-- url     : https://prove2.me/submissions/9d8d54e7-2b9d-4601-a18d-2e142ae61946

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A : Type*} [AddCommGroup A]
namespace GroundTheory.GroupCoh
theorem _root_.solution {f g : A →+ A} (hfg : ∀ x, f (g x) = 0) : g.range ≤ f.ker := by
  intro y hy
  obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.1 hy
  exact AddMonoidHom.mem_ker.2 (hfg x)
end GroundTheory.GroupCoh
