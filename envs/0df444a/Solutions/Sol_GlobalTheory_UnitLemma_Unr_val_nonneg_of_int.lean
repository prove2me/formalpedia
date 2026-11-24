-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.val_nonneg_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:52.627431+00:00
-- url     : https://prove2.me/submissions/4959d931-b3f4-4665-a880-221683ed04ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedInvolutionExtMapsIntegersToIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (K : UQ) (x : K.O) : 0 ≤ val K.O (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · rw [hx]; unfold val; simp
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) x
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega
end GlobalTheory.UnitLemma.Unr
