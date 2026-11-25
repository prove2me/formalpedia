-- Prove2me | solution 1 for GlobalTheory.GenericHom.hom_ext_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:53:30.485743+00:00
-- url     : https://prove2.me/submissions/3fe0b0d5-f882-4313-a64f-a51cd7e84e17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMonHomExtension
import Theorems.Thm_GlobalTheory_GenericHom_exists_point_mem
import Theorems.Thm_GlobalTheory_isNormalScheme_of_smooth


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
open GlobalTheory GlobalTheory.GenericHom
variable {k : Type} [Field k] [IsAlgClosed k]
namespace GlobalTheory.GenericHom
theorem _root_.solution {X Y : Over (Sp k)}
    [Smooth X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := isNormalScheme_of_smooth (S := Spec (.of k)) X.hom
  have : IsReduced X.left := IsNormalScheme.isReduced
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := k) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  obtain ⟨p, hp⟩ := exists_point_mem X {x} hx.isLocallyClosed ⟨x, rfl⟩
  have h1 : p.left ≫ f.left = p.left ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (p.left (IsLocalRing.closedPoint k)) =
      g.left (p.left (IsLocalRing.closedPoint k)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint k)) h1
  have h3 : p.left (IsLocalRing.closedPoint k) = x := hp _
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))
end GlobalTheory.GenericHom
