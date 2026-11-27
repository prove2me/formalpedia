-- Prove2me | solution 2 for GlobalTheory.gaussAbs_eq_gaussNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:47.420854+00:00
-- url     : https://prove2.me/submissions/5a03467f-9019-4f27-b09a-c0ccbd67be4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_le_gaussAbs
import Theorems.Thm_GlobalTheory_exists_gaussAbs_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {R σ τ : Type*} [CommRing R]
variable [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)
namespace GlobalTheory
theorem _root_.solution (f : MvPolynomial σ R) :
    gaussAbs a ha f = MvPowerSeries.gaussNorm a (fun _ => 1) (f : MvPowerSeries σ R) := by
  obtain ⟨m, hm⟩ := exists_gaussAbs_eq a ha f
  have hb : ∀ t : σ →₀ ℕ, a (MvPowerSeries.coeff t (f : MvPowerSeries σ R)) *
      t.prod ((fun _ : σ => (1 : ℝ)) · ^ ·) = a (coeff t f) := fun t => by
    simp [Finsupp.prod]
  rw [MvPowerSeries.gaussNorm]
  simp_rw [hb]
  refine le_antisymm (hm.le.trans (le_ciSup (f := fun t => a (coeff t f)) ⟨gaussAbs a ha f, ?_⟩ m))
    (ciSup_le fun t => le_gaussAbs a ha f t)
  rintro _ ⟨t, rfl⟩
  exact le_gaussAbs a ha f t
end GlobalTheory
