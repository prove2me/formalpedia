-- Prove2me | solution 1 for GlobalTheory.SegreCoord.box_exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:39:03.10316+00:00
-- url     : https://prove2.me/submissions/c085cd07-dd00-4103-86b4-56761aa40802

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
import Theorems.Thm_GlobalTheory_SegreCoord_loc_of_secCoord
import Theorems.Thm_GlobalTheory_SegreCoord_Loc_smul
import Theorems.Thm_GlobalTheory_SegreCoord_loc_box

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
theorem _root_.solution {β : R →+* T} {w : σ × σ → T} (hw : RankOne I β w) {i : σ × σ} (hi : IsUnit (w i)) :
    ∃ x : Sp T ⟶ Y, x ≫ p ≫ s = spMap β ∧ Loc (boxLB M p q) (boxTh th p q) x w := by
  obtain ⟨a, b⟩ := i
  obtain ⟨x₁, ⟨hx₁, h₁⟩, -⟩ := H.2.2 T β (fun i => w (i, b))
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) hi) (hw.2.1 b)
  obtain ⟨x₂, ⟨hx₂, h₂⟩, -⟩ := H.2.2 T β (fun i => w (a, i))
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨b, rfl⟩) hi) (hw.2.2 a)
  refine ⟨hP.lift x₁ x₂ (hx₁.trans hx₂.symm), by rw [hP.lift_fst_assoc, hx₁], ?_⟩
  obtain ⟨u, hu⟩ := hi
  have := (loc_box p q (x := hP.lift x₁ x₂ (hx₁.trans hx₂.symm)) (by rw [hP.lift_fst]; exact loc_of_secCoord h₁)
    (by rw [hP.lift_snd]; exact loc_of_secCoord h₂)).smul (u⁻¹).isUnit
  convert this using 2 with i
  rw [hw.1 i.1 b a i.2, ← hu, mul_comm (w _), Units.inv_mul_cancel_left]
end GlobalTheory.SegreCoord
