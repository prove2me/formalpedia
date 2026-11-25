-- Prove2me | solution 1 for GlobalTheory.SegreCoord.box_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:09:32.966171+00:00
-- url     : https://prove2.me/submissions/0bf93da6-e0a3-4d42-b8c6-ffaf87b4f09c

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
import Theorems.Thm_GlobalTheory_SegreCoord_Loc_unique
import Theorems.Thm_GlobalTheory_SegreCoord_unimod_mul
import Theorems.Thm_GlobalTheory_SegreCoord_rep_chart
import Theorems.Thm_GlobalTheory_SegreCoord_loc_box
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB


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
theorem _root_.solution {β : R →+* T} {x : Sp T ⟶ Y} (hx : x ≫ p ≫ s = spMap β) {w : σ × σ → T}
    (hw : Loc (boxLB M p q) (boxTh th p q) x w) {j k : M.ι} (hj : ∀ y, (x ≫ p) y ∈ M.U j) (hk : ∀ y, (x ≫ q) y ∈ M.U k) :
    ∃ (v₁ v₂ : σ → T) (t : T), IsUnit t ∧ (∀ i, w i = t * (v₁ i.1 * v₂ i.2)) ∧
      (Loc M th (x ≫ p) v₁ ∧ Ideal.span (Set.range v₁) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v₁ F = 0) ∧
      (Loc M th (x ≫ q) v₂ ∧ Ideal.span (Set.range v₂) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v₂ F = 0) := by
  obtain ⟨v₁, h₁⟩ := rep_chart H (x := x ≫ p) (β := β) (by rw [Category.assoc, hx]) hj
  obtain ⟨v₂, h₂⟩ := rep_chart H (x := x ≫ q) (β := β) (by rw [Category.assoc, ← hP.w, hx]) hk
  obtain ⟨t, ht, e⟩ := Loc.unique (DVR.linComb_isLB _ H.1 _ _) (loc_box p q h₁.1 h₂.1) hw (unimod_mul h₁.2.1 h₂.2.1)
  exact ⟨v₁, v₂, t, ht, e, h₁, h₂⟩
end GlobalTheory.SegreCoord
