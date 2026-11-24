-- Prove2me | solution 1 for GlobalTheory.SqZero.zpow_eq_one_of_mem_redKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:16.069616+00:00
-- url     : https://prove2.me/submissions/c924421c-248f-4966-92fd-da710f786779

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
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
namespace GlobalTheory.SqZero
theorem _root_.solution (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) {k : ℤ}
    (hk : ∀ a ∈ J, k • a = 0) {y : sp A ⟶ G} (hy : y ∈ redKer G J) : y ^ k = 1 := by
  have hc : k • kerEquiv hv hJ (Additive.ofMul (⟨y, hy⟩ : redKer (R := R) G J)) = 0 := by
    funext i
    apply Subtype.ext
    simp [hk _ (kerEquiv hv hJ (Additive.ofMul (⟨y, hy⟩ : redKer (R := R) G J)) i).2]
  have h1 : k • Additive.ofMul (⟨y, hy⟩ : redKer (R := R) G J) = 0 := by
    apply (kerEquiv hv hJ).injective
    rw [map_zsmul, map_zero]
    exact hc
  have h2 := congrArg (fun z => ((Additive.toMul z : redKer (R := R) G J) : sp A ⟶ G)) h1
  simpa using h2
end GlobalTheory.SqZero
