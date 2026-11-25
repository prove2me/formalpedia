-- Prove2me | solution 1 for GlobalTheory.UnifLieBasis.isDiff_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:47.310695+00:00
-- url     : https://prove2.me/submissions/f8baf51e-2e2b-4d16-afc0-d71be4068d48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLieBasisOfHolUnif
import Theorems.Thm_GlobalTheory_UnifLieBasis_snd_evalPt_mul
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_mem_iff
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
theorem _root_.solution {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v)
    (hv' : IsTan (R := ℂ) (G := A) v') (hd : u.IsDiff w v) (hd' : u.IsDiff w' v') : u.IsDiff (w + w') (v * v') := by
  intro U h'' f
  have ht := Chart.isTan_mul hv hv'
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 ht) U).1 h''
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  have h' := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv') U).2 h0
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← hv]
    exact fun p _ => h (Set.mem_univ _)
  rw [map_add, ← hd U h f, ← hd' U h' f]
  exact snd_evalPt_mul hv hv' U h1 h h' h'' f
end GlobalTheory.UnifLieBasis
