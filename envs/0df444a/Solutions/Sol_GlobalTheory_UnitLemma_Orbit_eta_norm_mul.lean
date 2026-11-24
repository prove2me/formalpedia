-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.eta_norm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:21:14.625802+00:00
-- url     : https://prove2.me/submissions/78e2be4d-3f2c-4e80-a8e3-06f37fc8b9db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_valuation_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (d x : K.E) (hd : d ≠ 0) : K.eta (d * x * K.c d) = K.eta x := by
  by_cases hx : x = 0
  · simp [hx]
  unfold UQ.eta val
  have hd' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E d ≠ 0 := by simpa using hd
  have hx' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  rw [map_mul, map_mul, valuation_conj, WithZero.log_mul (mul_ne_zero hd' hx') hd', WithZero.log_mul hd' hx']
  generalize WithZero.log ((IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E d) = a
  generalize WithZero.log ((IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x) = b
  rw [show -(a + b + a) = -b + 2 * (-a) by ring, zpow_add₀ (by norm_num), zpow_mul]
  norm_num
end GlobalTheory.UnitLemma.Orbit
