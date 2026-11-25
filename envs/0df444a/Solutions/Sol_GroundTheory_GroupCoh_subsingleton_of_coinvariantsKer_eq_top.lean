-- Prove2me | solution 1 for GroundTheory.GroupCoh.subsingleton_of_coinvariantsKer_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:25.799211+00:00
-- url     : https://prove2.me/submissions/2fe1b139-b3b6-4b13-965c-2b5d9a94015e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
import Theorems.Thm_GroundTheory_GroupCoh_eq_top_of_sup_coinvariantsKer_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open Representation
variable {k G V : Type*} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]
namespace GroundTheory.GroupCoh
theorem _root_.solution (hG : IsPGroup p G) (ρ : Representation k G V)
    (h : Coinvariants.ker ρ = ⊤) : Subsingleton V := by
  have hbot := eq_top_of_sup_coinvariantsKer_eq_top hG ρ ⊥ (fun _ => bot_le) (by rw [bot_sup_eq, h])
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Submodule k V) := hbot ▸ Submodule.mem_top
  have hy : y ∈ (⊥ : Submodule k V) := hbot ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at hx hy
  rw [hx, hy]
end GroundTheory.GroupCoh
