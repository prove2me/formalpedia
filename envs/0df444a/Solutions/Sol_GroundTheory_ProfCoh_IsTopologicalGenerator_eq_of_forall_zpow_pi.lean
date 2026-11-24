-- Prove2me | solution 1 for GroundTheory.ProfCoh.IsTopologicalGenerator.eq_of_forall_zpow_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:36.326522+00:00
-- url     : https://prove2.me/submissions/34af808e-790b-4b57-aaae-58a69a1f2744

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs
import Theorems.Thm_IsLocallyConstant_eq_of_eqOn_dense

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
variable {G : Type*} [Group G] [TopologicalSpace G]
open GroundTheory.ProfCoh.IsTopologicalGenerator
variable {σ : G}
namespace GroundTheory.ProfCoh.IsTopologicalGenerator
theorem _root_.solution (hσ : IsTopologicalGenerator σ) {n : ℕ} {Y : Type*}
    {f g : (Fin n → G) → Y} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (h : ∀ m : Fin n → ℤ, f (fun i => σ ^ m i) = g (fun i => σ ^ m i)) : f = g := by
  refine hf.eq_of_eqOn_dense hg (s := Set.univ.pi fun _ => (Subgroup.zpowers σ : Set G))
    (dense_pi Set.univ fun _ _ => hσ) fun x hx => ?_
  choose m hm using fun i => hx i (Set.mem_univ i)
  have hx' : x = fun i => σ ^ m i := funext fun i => (hm i).symm
  rw [hx']
  exact h m
end GroundTheory.ProfCoh.IsTopologicalGenerator
