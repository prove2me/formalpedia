-- Prove2me | solution 1 for GlobalTheory.TorsionDivisible.hom_ext_of_rationalPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:03:02.738412+00:00
-- url     : https://prove2.me/submissions/5086ef63-51bc-41d1-b23e-8fb410dd515b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyTorsionFiniteEndomorphismDivisible

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
open GlobalTheory GlobalTheory.TorsionDivisible
namespace GlobalTheory.TorsionDivisible
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] {X Y : Over (Sp K)}
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsProper Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp K)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  let p : 𝟙_ (Over (Sp K)) ⟶ X :=
    Over.homMk (pointOfClosedPoint (K := K) X.hom x hx) (pointOfClosedPoint_comp (K := K) X.hom x hx)
  have h1 : pointOfClosedPoint (K := K) X.hom x hx ≫ f.left =
      pointOfClosedPoint (K := K) X.hom x hx ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) =
      g.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint K)) h1
  have h3 := pointOfClosedPoint_apply (K := K) X.hom x hx (IsLocalRing.closedPoint K)
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))
end GlobalTheory.TorsionDivisible
