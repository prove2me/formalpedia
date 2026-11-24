-- Prove2me | solution 1 for GlobalTheory.SqZero.kerEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:32.530805+00:00
-- url     : https://prove2.me/submissions/7b78fc7a-c040-4af0-8f21-51dca8819e0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_kerEquiv_eq_iff
import Theorems.Thm_GlobalTheory_SqZero_eq_lieExp_kerEquiv
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_comp_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_lieExp_congr
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
theorem _root_.solution (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) {J' : Ideal A'}
    (hJ' : J' ^ 2 = ⊥) (φ : A →ₐ[R] A') (hφ : ∀ a ∈ J, φ a ∈ J') (y : redKer (R := R) G J)
    (i : Fin n) :
    (kerEquiv hv hJ' (Additive.ofMul ⟨spMap φ ≫ y.1, comp_mem_redKer y.2 φ hφ⟩) i : A') =
      φ (kerEquiv hv hJ (Additive.ofMul y) i) := by
  have hy := eq_lieExp_kerEquiv hv hJ y
  have key : kerEquiv hv hJ' (Additive.ofMul ⟨spMap φ ≫ y.1, comp_mem_redKer y.2 φ hφ⟩) =
      fun i => ⟨φ (kerEquiv hv hJ (Additive.ofMul y) i), hφ _ (kerEquiv hv hJ (Additive.ofMul y) i).2⟩ := by
    rw [kerEquiv_eq_iff]
    show spMap φ ≫ (y : sp A ⟶ G) = _
    rw [hy]
    refine (comp_lieExp v φ _ _).trans ?_
    exact lieExp_congr v (fun _ => rfl) _ _
  rw [key]
end GlobalTheory.SqZero
