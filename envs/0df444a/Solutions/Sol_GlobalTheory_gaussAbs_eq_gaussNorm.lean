-- Prove2me | solution 1 for GlobalTheory.gaussAbs_eq_gaussNorm
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:07:35.894824+00:00
-- url     : https://prove2.me/submissions/20414a62-2093-4112-b4b2-1127b1a3fb84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
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

theorem solution (f : MvPolynomial σ R) :
    gaussAbs a ha f = MvPowerSeries.gaussNorm a (fun _ => 1) (f : MvPowerSeries σ R) := by
  rw [gaussAbs_apply, MvPowerSeries.gaussNorm]
  have hprod (t : σ →₀ ℕ) : t.prod (fun _ n => (1 : ℝ) ^ n) = 1 := by
    simp [Finsupp.prod]
  simp_rw [hprod, mul_one, coeff_coe]
  set v := absValuation a ha
  have hle (t : σ →₀ ℕ) : a (coeff t f) ≤ (gaussVal v f : ℝ) := by
    rw [← coe_absValuation a ha]
    exact_mod_cast le_gaussVal v f t
  have hbd : BddAbove (Set.range fun t : σ →₀ ℕ => a (coeff t f)) :=
    ⟨(gaussVal v f : ℝ), by rintro _ ⟨t, rfl⟩; exact hle t⟩
  refine le_antisymm ?_ ?_
  · by_cases hf : f = 0
    · subst hf
      simp [a.map_zero]
    · have hc : AddMonoidAlgebra.coeff f ≠ 0 :=
        AddMonoidAlgebra.coeff_eq_zero.not.mpr hf
      obtain ⟨i, -, hi⟩ := exists_mem_support_coeffSup_eq (N := v) hc
      have hval : (gaussVal v f : ℝ) = a (coeff i f) := by
        have : gaussVal v f = v (coeff i f) := by
          simpa [gaussVal, gaussValAlg, MvPolynomial.coeff] using hi
        rw [this, coe_absValuation]
      rw [hval]
      exact le_ciSup hbd i
  · exact ciSup_le hle
