-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:40.808616+00:00
-- url     : https://prove2.me/submissions/46ff92c1-6206-4e97-90e5-935050c31a69

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (v : V) (g : G) : g ∈ stabilizer ρ v ↔ ρ g v = v :=
  Iff.rfl
end GroundTheory.ProfCoh
