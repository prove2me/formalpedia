-- Prove2me | solution 1 for GlobalTheory.OfPeriod.imPart_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:44.289835+00:00
-- url     : https://prove2.me/submissions/a63947f8-93ff-4bb1-9583-427f2e892ada

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
variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}
variable (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
  (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) {b : W →ₗ[ℝ] W} (hb : ∀ w, b w ∈ R)
  (hb' : ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im)
omit [IsScalarTower ℝ ℂ W]
include hpos hb hb'
namespace GlobalTheory.OfPeriod
theorem _root_.solution {w c : W} (hc : c ∈ R) (h : ∀ r ∈ R, (S c r).re = (S w r).im) : b w = c := by
  by_contra hne
  have h1 := hpos _ (sub_ne_zero.2 hne)
  have h2 := R.sub_mem (hb w) hc
  rw [map_sub S, LinearMap.sub_apply, hb' w _ h2, Complex.sub_re, h _ h2] at h1
  simp at h1
end GlobalTheory.OfPeriod
