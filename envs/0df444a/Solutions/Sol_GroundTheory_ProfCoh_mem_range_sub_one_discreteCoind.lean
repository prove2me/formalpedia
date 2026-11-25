-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_range_sub_one_discreteCoind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:47.380467+00:00
-- url     : https://prove2.me/submissions/e6f7bb23-5f97-421e-afb7-af8d2f3c6e3c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_Procyclic
import Theorems.Thm_GroundTheory_ProfCoh_isAddTorsion_discreteCoind
import Theorems.Thm_GroundTheory_ProfCoh_isZero_cohomology_discreteCoind


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
open CategoryTheory Limits groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
variable {σ : G}
namespace GroundTheory.ProfCoh
theorem _root_.solution (hσ : IsZHatGenerator σ) (A : Rep.{u} k G)
    [IsDiscreteRep A] (hA : IsAddTorsion A) (c : LocallyConstant G A) :
    c ∈ LinearMap.range ((discreteCoind k G A).ρ σ - 1) := by
  have hz := isZero_cohomology_discreteCoind k G A 0
  have hs : Subsingleton (cohomology (discreteCoind k G A) 1) :=
    ModuleCat.subsingleton_of_isZero hz
  obtain ⟨x, hx⟩ := H1Eval_surjective (discreteCoind k G A) hσ
    (isAddTorsion_discreteCoind (G := G) A hA) (Submodule.Quotient.mk c)
  rw [Subsingleton.elim x 0, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at hx
  exact hx
end GroundTheory.ProfCoh
