-- Prove2me | solution 1 for GroundTheory.ProfCoh.coindShortComplex_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:07:17.341917+00:00
-- url     : https://prove2.me/submissions/863f6232-6a28-4223-8d56-9ec19b57ad99

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules

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
open CategoryTheory Filter Topology
universe u
variable (k G : Type u) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [AddCommGroup X] [Module k X]
variable {k G}
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{u} k G) [IsDiscreteRep A] :
    (coindShortComplex A).ShortExact where
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro f hf
    change Submodule.Quotient.mk (p := coindEmbeddingRange A) f = 0 at hf
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hf
    exact ⟨a, ha⟩
  mono_f := by
    change Mono (coindEmbedding A)
    infer_instance
  epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
end GroundTheory.ProfCoh
