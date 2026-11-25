-- Prove2me | solution 1 for GlobalTheory.OfPeriod.sub_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:24.661514+00:00
-- url     : https://prove2.me/submissions/edc73046-c34a-418b-83cf-a9b0908b7e34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Theorems.Thm_GlobalTheory_OfPeriod_reForm_apply
import Theorems.Thm_GlobalTheory_AnArc_div_two_I
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
variable {O : Type} [CommRing O] [StarRing O] {ρ : O →+* Module.End ℂ W}
  (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w)) (hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R)
omit [IsScalarTower ℝ ℂ W]
include hconj hR hb
namespace GlobalTheory.OfPeriod
theorem _root_.solution {w w' u u' : W} (hu : ∀ r ∈ R, S u r = 0) (hu' : ∀ r ∈ R, S u' r = 0)
    (h : w = b (I • w) + I • b w + u) (h' : w' = b (I • w') + I • b w' + u') :
    S w (b w') - S u u' / (2 * I) = S w' (b w) - S u' u / (2 * I) - (S w w').im := by
  have hv : ∀ r ∈ R, S r u' = 0 := fun r hr => by rw [← hconj, hu' r hr, map_zero]
  have hre : ∀ z z', (S z z').re = (S z' z).re := fun z z' => by rw [← hconj z z', conj_re]
  have him : ∀ z z', (S z z').im = -(S z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  generalize b (I • w) = a, hb (I • w) = ha at h
  generalize b (I • w') = a', hb (I • w') = ha' at h'
  generalize b w = c, hb w = hc at h ⊢
  generalize b w' = c', hb w' = hc' at h' ⊢
  subst h h'
  simp only [map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu _ ha', hu _ hc',
    hu' _ hc, hv _ ha, hv _ hc, AnArc.div_two_I]
  apply Complex.ext <;>
    simp [hR _ ha _ ha', hR _ ha _ hc', hR _ hc _ ha', hR _ hc _ hc', hR _ ha' _ hc, hR _ hc' _ hc, hre a' c, hre c' c,
      hre u' u, him u' u]
  ring
end GlobalTheory.OfPeriod
