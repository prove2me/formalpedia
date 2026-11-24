-- Prove2me | solution 1 for GlobalTheory.SS.LiftTorus.subsingleton_pic_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:17:58.16634+00:00
-- url     : https://prove2.me/submissions/617c2b21-b1b7-4a96-bab5-027a6e7e10c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusGamma_bijective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LiftTorus
open GlobalTheory.TorsorUnit
namespace GlobalTheory.SS.LiftTorus
theorem _root_.solution (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] :
    Subsingleton (CommRing.Pic Γ((splitTorus (Sp k) X).left, ⊤)) := by
  have := GlobalTheory.subsingleton_pic_addMonoidAlgebra_of_free k X
  let e : Γ((splitTorus (Sp k) X).left, ⊤) ≃+* AddMonoidAlgebra k X :=
    RingEquiv.ofBijective (Rosenlicht.torusGamma k X).hom (Rosenlicht.torusGamma_bijective k X)
  have key : ∀ x : CommRing.Pic Γ((splitTorus (Sp k) X).left, ⊤), x =
      CommRing.Pic.mapRingHom e.symm.toRingHom (CommRing.Pic.mapRingHom e.toRingHom x) := fun x => by
    rw [CommRing.Pic.mapRingHom_mapRingHom, e.symm_toRingHom_comp_toRingHom,
      CommRing.Pic.mapRingHom_id_apply]
  refine ⟨fun x y => ?_⟩
  rw [key x, key y, Subsingleton.elim (CommRing.Pic.mapRingHom e.toRingHom x) _]
end GlobalTheory.SS.LiftTorus
