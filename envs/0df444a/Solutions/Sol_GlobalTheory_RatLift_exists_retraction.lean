-- Prove2me | solution 1 for GlobalTheory.RatLift.exists_retraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:43.835014+00:00
-- url     : https://prove2.me/submissions/74625ecc-d898-4ea3-84ef-b33622fac2c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsLiftOfRetraction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RatLift
namespace GlobalTheory.RatLift
theorem _root_.solution {A C X : Type} [CommRing A] [CommRing C] [AddCommGroup X] (f : A →+* C)
    (g : Multiplicative X →* C)
    (h : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g (fun _ _ => Commute.all _ _))) :
    ∃ r : C →+* A, r.comp f = RingHom.id A := by
  let e := RingEquiv.ofBijective _ h
  let a : AddMonoidAlgebra A X →+* A :=
    AddMonoidAlgebra.liftNCRingHom (RingHom.id A) (1 : Multiplicative X →* A) (fun _ _ => Commute.all _ _)
  refine ⟨a.comp e.symm.toRingHom, RingHom.ext fun c => ?_⟩
  have : e.symm (f c) = AddMonoidAlgebra.single 0 c := by
    rw [RingEquiv.symm_apply_eq]
    simp [e, AddMonoidAlgebra.liftNCRingHom]
  simp [this, a, AddMonoidAlgebra.liftNCRingHom]
end GlobalTheory.RatLift
