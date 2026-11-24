-- Prove2me | solution 1 for GlobalTheory.SqZero.IsLiftAlong.mul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:27.878007+00:00
-- url     : https://prove2.me/submissions/149dbe44-1667-4a64-8cf4-c4b66c36050e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
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
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
variable {J : Ideal A} {T T' : Type} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
omit [Smooth G.hom]
namespace GlobalTheory.SqZero
namespace IsLiftAlong
theorem _root_.solution {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ G} {φ : A →ₐ[R] T} {y y' : sp T ⟶ G}
    (h : IsLiftAlong y₀ φ y) (h' : IsLiftAlong y₀ φ y') : y * y'⁻¹ ∈ redKer G (J.map φ) := by
  have e : ∀ w, IsLiftAlong y₀ φ w → spMap (Ideal.Quotient.mkₐ R (J.map φ)) ≫ w =
      spMap (Ideal.quotientMapₐ (J.map φ) φ Ideal.le_comap_map) ≫ y₀ := fun w hw =>
    hw _ _ _ (by ext a; rfl)
  show y * y'⁻¹ ∈ (pointsMap G (Ideal.Quotient.mkₐ R (J.map φ))).ker
  rw [MonoidHom.mem_ker, map_mul, map_inv, ptsMap_apply, ptsMap_apply, e y h, e y' h', mul_inv_cancel]
end IsLiftAlong
end GlobalTheory.SqZero
