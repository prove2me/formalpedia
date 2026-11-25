-- Prove2me | solution 1 for GlobalTheory.SegreCoord.box_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:32.413583+00:00
-- url     : https://prove2.me/submissions/cfc1d92e-8f27-4f22-9d27-753966bb3b6a

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
import Theorems.Thm_GlobalTheory_SegreCoord_loc_of_away
import Theorems.Thm_GlobalTheory_SegreCoord_box_unique
import Theorems.Thm_GlobalTheory_SegreCoord_box_exists_unit
import Theorems.Thm_GlobalTheory_SegreCoord_RankOne_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
theorem _root_.solution {β : R →+* T} {w : σ × σ → T} (hs : Ideal.span (Set.range w) = ⊤) (hw : RankOne I β w) :
    ∃ x : Sp T ⟶ Y, x ≫ p ≫ s = spMap β ∧ Loc (boxLB M p q) (boxTh th p q) x w := by
  choose x hx hl using fun i : σ × σ => box_exists_unit H hP (hw.map (algebraMap T (Localization.Away (w i))))
    (i := i) (IsLocalization.Away.algebraMap_isUnit _)
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of T) w hs).openCover
  have hc : ∀ i j : σ × σ, pullback.fst (𝒰.f i) (𝒰.f j) ≫ x i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ x j := by
    intro i j
    let A := Localization.Away (w i)
    let B := Localization.Away (w j)
    refine (cancel_epi (pullbackSpecIso T A B).inv).1 ?_
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    refine (congrArg (· ≫ x i) (pullbackSpecIso_inv_fst T A B)).trans
      (Eq.trans ?_ (congrArg (· ≫ x j) (pullbackSpecIso_inv_snd T A B)).symm)
    let l : A →+* A ⊗[T] B := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* A ⊗[T] B := (Algebra.TensorProduct.includeRight (R := T) (A := A) (B := B)).toRingHom
    have e : l.comp (algebraMap T A) = r.comp (algebraMap T B) :=
      Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    show spMap l ≫ x i = spMap r ≫ x j
    refine box_unique H hP (β := (l.comp (algebraMap T A)).comp β) ?_ ?_ ((hl i).baseChange l) ?_
    · rw [Category.assoc, hx, ← spMap_comp, RingHom.comp_assoc]
    · rw [Category.assoc, hx, ← spMap_comp, e, RingHom.comp_assoc]
    · convert (hl j).baseChange r using 2 with k
      exact congrArg (fun φ : T →+* A ⊗[T] B => φ (w k)) e
  have hg : ∀ i : σ × σ, spMap (algebraMap T (Localization.Away (w i))) ≫ 𝒰.glueMorphisms x hc = x i :=
    fun i => 𝒰.ι_glueMorphisms x hc i
  refine ⟨𝒰.glueMorphisms x hc, 𝒰.hom_ext _ _ fun i => ?_, loc_of_away fun y => ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p ≫ s) (hg i)).trans ((hx i).trans (spMap_comp _ _)))
  · obtain ⟨i, hi⟩ : ∃ i, w i ∉ y.asIdeal := by
      by_contra hn
      push Not at hn
      exact y.isPrime.ne_top (eq_top_iff.2 (hs ▸ Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hn i)))
    exact ⟨w i, hi, by rw [hg]; exact hl i⟩
end GlobalTheory.SegreCoord
