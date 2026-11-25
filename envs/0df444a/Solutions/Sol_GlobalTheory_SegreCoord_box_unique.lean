-- Prove2me | solution 1 for GlobalTheory.SegreCoord.box_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:30:25.593489+00:00
-- url     : https://prove2.me/submissions/5baa9c0b-1867-49f0-8f1d-96ffd122a799

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Theorems.Thm_GlobalTheory_SegreCoord_Loc_baseChange
import Theorems.Thm_GlobalTheory_SegreCoord_Loc_smul
import Theorems.Thm_GlobalTheory_SegreCoord_exists_away
import Theorems.Thm_GlobalTheory_SegreCoord_hom_ext_away
import Theorems.Thm_GlobalTheory_SegreCoord_exists_unit_of_mul_eq
import Theorems.Thm_GlobalTheory_SegreCoord_rep_unique
import Theorems.Thm_GlobalTheory_SegreCoord_box_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
variable {R : Type} [CommRing R] (I : Ideal (MvPolynomial σ R))
variable {I} {s : X ⟶ Sp R} (H : ProjRep I s M th) {Y : Scheme.{0}} {p q : Y ⟶ X} (hP : IsPullback p q s s)
include H hP
namespace GlobalTheory.SegreCoord
theorem _root_.solution {β : R →+* T} {x x' : Sp T ⟶ Y} (hx : x ≫ p ≫ s = spMap β) (hx' : x' ≫ p ≫ s = spMap β)
    {w : σ × σ → T} (hw : Loc (boxLB M p q) (boxTh th p q) x w) (hw' : Loc (boxLB M p q) (boxTh th p q) x' w) :
    x = x' := by
  refine hom_ext_away fun y => ?_
  obtain ⟨j, hj⟩ := exists_chart H.1 ((x ≫ p) y)
  obtain ⟨k, hk⟩ := exists_chart H.1 ((x ≫ q) y)
  obtain ⟨j', hj'⟩ := exists_chart H.1 ((x' ≫ p) y)
  obtain ⟨k', hk'⟩ := exists_chart H.1 ((x' ≫ q) y)
  obtain ⟨f, hf, hW⟩ := exists_away (((x ≫ p) ⁻¹ᵁ M.U j ⊓ (x ≫ q) ⁻¹ᵁ M.U k) ⊓
    ((x' ≫ p) ⁻¹ᵁ M.U j' ⊓ (x' ≫ q) ⁻¹ᵁ M.U k')) y ⟨⟨hj, hk⟩, hj', hk'⟩
  refine ⟨f, hf, ?_⟩
  have b : (spMap (algebraMap T (Localization.Away f)) ≫ x) ≫ p ≫ s =
      spMap ((algebraMap T (Localization.Away f)).comp β) := by rw [Category.assoc, hx, ← spMap_comp]
  have b' : (spMap (algebraMap T (Localization.Away f)) ≫ x') ≫ p ≫ s =
      spMap ((algebraMap T (Localization.Away f)).comp β) := by rw [Category.assoc, hx', ← spMap_comp]
  obtain ⟨v₁, v₂, t, ht, e, h₁, h₂⟩ := box_local H hP b (hw.baseChange (algebraMap T (Localization.Away f)))
    (fun z => (hW z).1.1) (fun z => (hW z).1.2)
  obtain ⟨w₁, w₂, t', ht', e', k₁, k₂⟩ := box_local H hP b' (hw'.baseChange (algebraMap T (Localization.Away f)))
    (fun z => (hW z).2.1) (fun z => (hW z).2.2)
  obtain ⟨t', rfl⟩ := ht'
  have ee : ∀ i j, w₁ i * w₂ j = ((t'⁻¹).val * t) * (v₁ i * v₂ j) := fun i j => by
    rw [mul_assoc, ← e (i, j), e' (i, j), Units.inv_mul_cancel_left]
  obtain ⟨u₁, hu₁, e₁⟩ := exists_unit_of_mul_eq k₁.2.1 k₂.2.1 ee
  obtain ⟨u₂, hu₂, e₂⟩ := exists_unit_of_mul_eq (v₁ := v₂) (v₂ := v₁) (t := (t'⁻¹).val * t) k₂.2.1 k₁.2.1
    fun i j => by rw [mul_comm, ee, mul_comm (v₂ i)]
  refine hP.hom_ext (rep_unique H ((Category.assoc _ _ _).trans b) ((Category.assoc _ _ _).trans b') k₁.2.1 ?_ k₁.1)
    (rep_unique H (β := (algebraMap T (Localization.Away f)).comp β) (by rw [Category.assoc, ← hP.w, b])
      (by rw [Category.assoc, ← hP.w, b']) k₂.2.1 ?_ k₂.1)
  · rw [funext e₁]; exact h₁.1.smul hu₁
  · rw [funext e₂]; exact h₂.1.smul hu₂
end GlobalTheory.SegreCoord
