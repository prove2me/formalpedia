-- Prove2me | solution 1 for GroundTheory.ProfCoh.IsTopologicalGenerator.eq_of_forall_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:06.538805+00:00
-- url     : https://prove2.me/submissions/e0e67b3c-e238-40b7-a645-b2df12584759

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
theorem _root_.solution (hσ : IsTopologicalGenerator σ) {Y : Type*} {f g : G → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) (h : ∀ n : ℤ, f (σ ^ n) = g (σ ^ n)) :
    f = g :=
  hf.eq_of_eqOn_dense hg hσ fun _ ⟨n, hn⟩ => hn ▸ h n
end GroundTheory.ProfCoh.IsTopologicalGenerator
