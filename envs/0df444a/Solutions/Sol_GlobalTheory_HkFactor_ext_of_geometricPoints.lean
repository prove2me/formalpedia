-- Prove2me | solution 1 for GlobalTheory.HkFactor.ext_of_geometricPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:11:26.305909+00:00
-- url     : https://prove2.me/submissions/475137e3-228e-4713-97ea-13eb0a3ebac8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_KerScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueFactorThroughEtaleIsogenyReduced
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
open GlobalTheory GlobalTheory.HkFactor
namespace GlobalTheory.HkFactor
theorem _root_.solution {T X Z : Scheme.{0}} [IsReduced T] (q : X ⟶ Z) [IsSeparated q]
    (f g : T ⟶ X) (h : f ≫ q = g ≫ q)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), x ≫ f = x ≫ g) : f = g := by
  classical

  let K : T → Type := fun t => AlgebraicClosure (T.residueField t)
  let pts : (∐ fun t : T => Sp (K t)) ⟶ T := Sigma.desc fun t =>
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) (K t))) ≫ T.fromSpecResidueField t

  have : Surjective pts := by
    refine ⟨fun t => ⟨Sigma.ι (fun t : T => Sp (K t)) t (IsLocalRing.closedPoint (K t)), ?_⟩⟩
    have e : (Sigma.ι (fun t : T => Sp (K t)) t ≫ pts) (IsLocalRing.closedPoint (K t)) = t := by
      simp only [pts, Sigma.ι_desc]
      exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e
  refine ext_of_isDominant_of_isSeparated q h pts ?_
  refine Sigma.hom_ext _ _ fun t => ?_
  simpa only [pts, Sigma.ι_desc_assoc] using H (K t) _
end GlobalTheory.HkFactor
