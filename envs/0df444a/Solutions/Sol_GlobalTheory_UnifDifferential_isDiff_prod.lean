-- Prove2me | solution 1 for GlobalTheory.UnifDifferential.isDiff_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:00:16.476324+00:00
-- url     : https://prove2.me/submissions/b5d0689a-d369-4831-8182-aafa8d061354

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Theorems.Thm_GlobalTheory_UnifDifferential_isDiff_mul
import Theorems.Thm_GlobalTheory_UnifDifferential_isDiff_one
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp IsTan fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.SqZero
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.UnifDifferential
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A]
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.UnifDifferential
theorem _root_.solution : ∀ {n : ℕ} (W : Fin n → Fin g → ℂ) (v : Fin n → (epsR ℂ ⟶ A)),
    (∀ i, IsTan (v i)) → (∀ i, u.IsDiff (W i) (v i)) →
      IsTan (List.ofFn v).prod ∧ u.IsDiff (∑ i, W i) (List.ofFn v).prod
  | 0, W, v, _, _ => by
    rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨isTan_one, isDiff_one u⟩
  | n + 1, W, v, hv, h => by
    obtain ⟨h₁, h₂⟩ := solution (fun i => W i.succ) (fun i => v i.succ) (fun i => hv _) (fun i => h _)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨isTan_mul (hv 0) h₁, isDiff_mul u (hv 0) h₁ (h 0) h₂⟩
end GlobalTheory.UnifDifferential
