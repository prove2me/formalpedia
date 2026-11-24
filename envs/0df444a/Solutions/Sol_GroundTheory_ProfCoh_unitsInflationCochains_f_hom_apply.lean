-- Prove2me | solution 1 for GroundTheory.ProfCoh.unitsInflationCochains_f_hom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:59:17.77875+00:00
-- url     : https://prove2.me/submissions/616b809d-25af-493d-9505-01fb4cd8358e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply

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
open CategoryTheory groupCohomology
universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable {K L}
variable [IsGalois K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution (E : IntermediateField K L) [FiniteDimensional K E]
    [Normal K E] (n : ℕ) (x : (Fin n → Gal(E/K)) → Additive Eˣ) (g : Fin n → Gal(L/K)) :
    ((cochainsComplexι (galUnits.{u} K L)).f n).hom (((unitsInflationCochains E).f n).hom x) g =
      (unitsRestrictHom E).hom (x fun i => AlgEquiv.restrictNormalHom E (g i)) :=
  rfl
end GroundTheory.ProfCoh
