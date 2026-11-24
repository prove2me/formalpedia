-- Prove2me | solution 1 for GlobalTheory.JacGen.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:50:06.659678+00:00
-- url     : https://prove2.me/submissions/cafffbd9-dc20-4211-9491-e2b0309ed00e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacGen
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))}
namespace GlobalTheory.JacGen
theorem _root_.solution {y : G.left} [Algebra K (G.left.presheaf.stalk y)]
    (j : sp (R₀ := K) (G.left.presheaf.stalk y) ⟶ G) (hj : j.left = G.left.fromSpecStalk y)
    {T : Type} [CommRing T] [IsLocalRing T] [Algebra K T] (w : sp (R₀ := K) T ⟶ G)
    (hw : w.left (closedPoint T) = y) : ∃ φ : G.left.presheaf.stalk y →ₐ[K] T, spMap φ ≫ j = w := by
  obtain ⟨φ, hφ⟩ : ∃ φ : G.left.presheaf.stalk y ⟶ .of T, Spec.map φ ≫ G.left.fromSpecStalk y = w.left := by
    subst hw
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of T) w.left⟩
  have h : CommRingCat.ofHom (algebraMap K (G.left.presheaf.stalk y)) ≫ φ =
      CommRingCat.ofHom (algebraMap K T) := by
    apply Spec.map_injective
    have h1 := Over.w j
    have h2 := Over.w w
    rw [hj] at h1
    rw [← hφ] at h2
    rw [Spec.map_comp]
    exact (congrArg (Spec.map φ ≫ ·) h1.symm).trans ((Category.assoc _ _ _).symm.trans h2)
  refine ⟨{ φ.hom with commutes' := fun a => congrArg (fun q => q.hom a) h }, ?_⟩
  apply Over.OverMorphism.ext
  rw [Over.comp_left, hj]
  exact hφ
end GlobalTheory.JacGen
