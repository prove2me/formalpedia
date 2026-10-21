-- Prove2me | solution 1 for MazurTransfer.original_scheme_pullback_product_points_naturality
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T01:16:12.777508+00:00
-- url     : https://prove2.me/submissions/1b36c687-08b2-4584-89e5-583b4fffa295

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original pullback product point equivalence over the same fixed base retains every precomposition map and both original structure morphisms.
Named downstream consumer: the principal-action scheme isomorphism for the actual integral nineteen norm-preimage torsor.
-/
import Definitions.Def_MazurTransfer_OriginalSchemePullbackProductPointsData20261020
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open MazurTransfer.SchemePullbackProductPoints
universe u
namespace MazurTransfer.OriginalSchemePullbackProductPointsBoundary20261020
end MazurTransfer.OriginalSchemePullbackProductPointsBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pullback product points over a FIXED base, with EVERY
precomposition map. No change of the given structure morphisms.
Named downstream consumer: the actual integral norm-preimage torsor's
principal-action scheme isomorphism.
-/

noncomputable section
namespace MazurTransfer.OriginalSchemePullbackProductPointsProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
variable {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)



variable {T : Scheme.{u}} (t : T ⟶ B)







variable {T' : Scheme.{u}} (t' : T' ⟶ B) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')

theorem pointsEquiv_natural (b : SchemeHomOver t (productStr f g)) :
    pointsEquiv f g t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b) =
      (GoodReductionJacobian.schemeHomOverComp ψ hψ (pointsEquiv f g t b).1,
       GoodReductionJacobian.schemeHomOverComp ψ hψ (pointsEquiv f g t b).2) := by
  apply Prod.ext
  · exact Subtype.ext (Category.assoc _ _ _)
  · exact Subtype.ext (Category.assoc _ _ _)

end MazurTransfer.OriginalSchemePullbackProductPointsProof20261020

theorem solution : (∀ {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) {T : Scheme.{u}} (t : T ⟶ B) {T' : Scheme.{u}} (t' : T' ⟶ B) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'), ∀ (b : SchemeHomOver t (productStr f g)),
pointsEquiv f g t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b) =
      (GoodReductionJacobian.schemeHomOverComp ψ hψ (pointsEquiv f g t b).1,
       GoodReductionJacobian.schemeHomOverComp ψ hψ (pointsEquiv f g t b).2)) := by
  exact MazurTransfer.OriginalSchemePullbackProductPointsProof20261020.pointsEquiv_natural
#print axioms solution
