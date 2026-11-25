-- Prove2me | solution 1 for GlobalTheory.ZM.SegreCoord.hom_ext_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:53:16.588796+00:00
-- url     : https://prove2.me/submissions/a39492e2-4042-48c2-9f14-8349fa1452a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SegreCoordinates
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.SegreCoord
open GlobalTheory.ZM.RepBC GlobalTheory.AbLaw.Segre
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec}
namespace GlobalTheory.ZM.SegreCoord
theorem _root_.solution {W Z : Scheme.{0}} {T₁ T₂ : Type} [CommRing T₁] [CommRing T₂]
    (a : W ⟶ Sp T₁) (b : W ⟶ Sp T₂) (f : Sp T₁ ⟶ Z) (g : Sp T₂ ⟶ Z)
    (h : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ W) (φ₁ : T₁ →+* T) (φ₂ : T₂ →+* T), y ≫ a = spMap φ₁ →
      y ≫ b = spMap φ₂ → spMap φ₁ ≫ f = spMap φ₂ ≫ g) : a ≫ f = b ≫ g := by
  refine W.affineOpenCover.openCover.hom_ext _ _ fun i => ?_
  let y : Sp (W.affineOpenCover.X i) ⟶ W := W.affineOpenCover.f i
  have := h _ y (Spec.preimage (y ≫ a)).hom (Spec.preimage (y ≫ b)).hom (Spec.map_preimage _).symm
    (Spec.map_preimage _).symm
  change y ≫ a ≫ f = y ≫ b ≫ g
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_preimage (y ≫ a), ← Spec.map_preimage (y ≫ b)]
  exact this
end GlobalTheory.ZM.SegreCoord
