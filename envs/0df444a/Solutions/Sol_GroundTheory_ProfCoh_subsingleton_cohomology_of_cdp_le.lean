-- Prove2me | solution 1 for GroundTheory.ProfCoh.subsingleton_cohomology_of_cdp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:29:05.25318+00:00
-- url     : https://prove2.me/submissions/c664df33-161e-4a69-adeb-d2db9b9af940

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_primaryComponent_cohomology_eq_bot_iff_of_nsmul
import Theorems.Thm_GroundTheory_ProfCoh_cdp_le_iff


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
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {p : ℕ} (hp : p.Prime) {n : ℕ} (h : cdp p G ≤ n)
    (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] (hA : ∀ a : A, p • a = 0) {q : ℕ}
    (hq : n < q) : Subsingleton (cohomology A q) :=
  (primaryComponent_cohomology_eq_bot_iff_of_nsmul A hA q).1
    (cdp_le_iff.1 h A (fun a => isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p, hp.pos, hA a⟩) q
      (by exact_mod_cast hq))
end GroundTheory.ProfCoh
