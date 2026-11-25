-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cechCondition_tilde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:57.322403+00:00
-- url     : https://prove2.me/submissions/b696aa1a-843a-4db4-8a16-4bc1e6f7f17f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cechAcyclic_of_localizingAction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry PrimeSpectrum
universe w u
variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution : CechCondition (X := (Spec R).toTopCat) IsBasicOpen (tildeAb M) := by
  rintro V ⟨g, rfl⟩ ι _ U hU hsup
  choose h hh using hU
  have : U = (fun r : R => (basicOpen r : Opens (Spec R).toTopCat)) ∘ h := funext hh
  subst this
  exact cechAcyclic_of_localizingAction (tildeAction M) h g hsup
end GroundTheory.Arith.SchemeCoh
