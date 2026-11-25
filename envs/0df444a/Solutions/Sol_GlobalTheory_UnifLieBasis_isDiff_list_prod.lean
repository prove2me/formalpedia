-- Prove2me | solution 1 for GlobalTheory.UnifLieBasis.isDiff_list_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:49:17.146397+00:00
-- url     : https://prove2.me/submissions/2c2b2139-70dd-47d3-ad4e-938e494634ac

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLieBasisOfHolUnif
import Theorems.Thm_GlobalTheory_UnifLieBasis_isDiff_add
import Theorems.Thm_GlobalTheory_UnifLieBasis_isDiff_zero
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UnifLieBasis
open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.UnifLieBasis
theorem _root_.solution : ∀ {k : ℕ} (w : Fin k → Fin g → ℂ) (v : Fin k → (epsR ℂ ⟶ A)),
    (∀ i, IsTan (R := ℂ) (G := A) (v i)) → (∀ i, u.IsDiff (w i) (v i)) →
    IsTan (R := ℂ) (G := A) (List.ofFn v).prod ∧ u.IsDiff (∑ i, w i) (List.ofFn v).prod
  | 0, w, v, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨Chart.isTan_one, isDiff_zero u⟩
  | k + 1, w, v, hv, hd => by
    obtain ⟨h1, h2⟩ := solution (fun i => w i.succ) (fun i => v i.succ) (fun i => hv _) (fun i => hd _)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨Chart.isTan_mul (hv 0) h1, isDiff_add u (hv 0) h1 (hd 0) h2⟩
end GlobalTheory.UnifLieBasis
