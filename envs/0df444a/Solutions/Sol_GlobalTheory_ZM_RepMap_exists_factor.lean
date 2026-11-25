-- Prove2me | solution 1 for GlobalTheory.ZM.RepMap.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:22:11.925778+00:00
-- url     : https://prove2.me/submissions/4576317c-682a-4b90-b4f9-21d2e1ae2b7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSchemeMapOfProjectiveCoordinates
import Theorems.Thm_GlobalTheory_ZM_RepMap_exists_spMap
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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepMap
variable {X : Scheme.{0}} {σ : Type}
namespace GlobalTheory.ZM.RepMap
theorem _root_.solution {U : Scheme.{0}} {R : Type} [CommRing R] (y : Sp R ⟶ X) (u : U ⟶ X) [IsOpenImmersion u]
    (p : Sp R) (h : y p ∈ Set.range u) : ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (a : Sp R' ⟶ U),
      IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ spMap φ ≫ y = a ≫ u := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := u) p q hq.symm
  obtain ⟨i, r, hr⟩ := (pullback y u).affineOpenCover.openCover.exists_eq z
  let C := (pullback y u).affineOpenCover.X i
  let w : Sp C ⟶ pullback y u := (pullback y u).affineOpenCover.f i
  have : IsOpenImmersion w := (pullback y u).affineOpenCover.map_prop i
  obtain ⟨φ, hφ⟩ := exists_spMap (w ≫ pullback.fst y u)
  refine ⟨C, inferInstance, φ, w ≫ pullback.snd y u, ?_, ?_, ?_⟩
  · rw [← hφ]; infer_instance
  · rw [← hφ]; refine ⟨r, ?_⟩
    rw [← hz, ← hr]; rfl
  · rw [← hφ, Category.assoc, Category.assoc, pullback.condition]
end GlobalTheory.ZM.RepMap
