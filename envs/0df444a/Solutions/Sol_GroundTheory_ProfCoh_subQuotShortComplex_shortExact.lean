-- Prove2me | solution 1 for GroundTheory.ProfCoh.subQuotShortComplex_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:47:27.653028+00:00
-- url     : https://prove2.me/submissions/4c1772e6-3922-4ff4-ac49-59efbb718227

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite

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
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
omit [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{u} k G) (W : Submodule k A)
    (h : ∀ g, W ≤ W.comap (A.ρ g)) : (subQuotShortComplex A W h).ShortExact where
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro a ha
    change Submodule.Quotient.mk (p := W) a = 0 at ha
    exact ⟨⟨a, (Submodule.Quotient.mk_eq_zero _).1 ha⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 Subtype.val_injective
  epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
end GroundTheory.ProfCoh
