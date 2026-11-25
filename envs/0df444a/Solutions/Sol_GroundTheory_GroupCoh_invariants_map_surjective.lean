-- Prove2me | solution 1 for GroundTheory.GroupCoh.invariants_map_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:45.557344+00:00
-- url     : https://prove2.me/submissions/03504611-789e-45b7-83e6-bb6d10519a2b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes

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
open CategoryTheory Limits groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G) (S : Subgroup G) [S.Normal]
namespace GroundTheory.GroupCoh
theorem _root_.solution {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (h1 : IsZero (groupCohomology X.X₁ 1)) :
    Function.Surjective ((invariantsFunctor k G).map X.g).hom := by
  have ex := (map_cochainsFunctor_shortExact hX).homology_exact₃ 0 1 rfl
  have e : Epi (map (MonoidHom.id G) X.g 0) := ex.epi_f (h1.eq_of_tgt _ _)
  have hc := map_id_comp_H0Iso_hom X.g
  have e2 : Epi ((H0Iso X.X₂).hom ≫ (invariantsFunctor k G).map X.g) := by
    rw [← hc]; infer_instance
  have e3 := epi_of_epi (H0Iso X.X₂).hom ((invariantsFunctor k G).map X.g)
  exact (ModuleCat.epi_iff_surjective _).1 e3
end GroundTheory.GroupCoh
