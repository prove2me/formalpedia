-- Prove2me | solution 1 for GlobalTheory.SqZero.kerEquiv_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:35.162939+00:00
-- url     : https://prove2.me/submissions/8191c251-7edc-42ea-8c57-1f81bad28aae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_kerEquiv_symm_apply
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
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
namespace GlobalTheory.SqZero
theorem _root_.solution (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥)
    (y : redKer (R := R) G J) (c : Fin n → J) : kerEquiv hv hJ (Additive.ofMul y) = c ↔
      (y : sp A ⟶ G) =
        lieExp v (fun i => (c i : A)) (fun i => mul_eq_zero_of_sq hJ (c i).2 (c i).2) := by
  constructor
  · rintro rfl
    have := kerEquiv_symm_apply hv hJ (kerEquiv hv hJ (Additive.ofMul y))
    rw [AddEquiv.symm_apply_apply] at this
    exact this
  · intro h
    rw [← AddEquiv.eq_symm_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [kerEquiv_symm_apply]
    exact h
end GlobalTheory.SqZero
