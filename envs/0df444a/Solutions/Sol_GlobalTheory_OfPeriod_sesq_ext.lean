-- Prove2me | solution 1 for GlobalTheory.OfPeriod.sesq_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:04:02.63261+00:00
-- url     : https://prove2.me/submissions/070c88fe-f2c2-4e89-9f5d-c1d0d2451695

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Theorems.Thm_GlobalTheory_OfPeriod_reForm_apply
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


attribute [local simp] GlobalTheory.OfPeriod.reForm_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
namespace GlobalTheory.OfPeriod
theorem _root_.solution {ι : Type} {v : ι → W} (hv : Submodule.span ℝ (Set.range v) = ⊤) {S S' : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ}
    (h : ∀ i k, (S (v i) (v k)).im = (S' (v i) (v k)).im) (x y : W) : S x y = S' x y := by
  have h1 : imForm S = imForm S' := LinearMap.ext_on_range hv fun i => LinearMap.ext_on_range hv fun k => h i k
  have h2 : ∀ x y, (S x y).im = (S' x y).im := fun x y => congr($h1 x y)
  exact Complex.ext (by simpa using h2 (I • x) y) (h2 x y)
end GlobalTheory.OfPeriod
