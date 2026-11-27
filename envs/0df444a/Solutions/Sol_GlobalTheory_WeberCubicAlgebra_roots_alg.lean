-- Prove2me | solution 1 for GlobalTheory.WeberCubicAlgebra.roots_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:30.174539+00:00
-- url     : https://prove2.me/submissions/c6d6e2f9-7325-4385-9ee1-fbb62315d7cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionsRootsOfCubicOfHalfPeriodDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open Polynomial
open UpperHalfPlane hiding I
noncomputable section
open GlobalTheory GlobalTheory.WeberCubicAlgebra
namespace GlobalTheory.WeberCubicAlgebra
theorem _root_.solution {e1 e2 e3 g h P A B D : ℂ} (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3)
    (r1 : 4 * e1 ^ 3 - g * e1 - h = 0) (r2 : 4 * e2 ^ 3 - g * e2 - h = 0)
    (r3 : 4 * e3 ^ 3 - g * e3 - h = 0)
    (d1 : e1 - e2 = P * A) (d2 : e1 - e3 = P * B) (d3 : e3 - e2 = P * D) :
    g = 2 / 3 * P ^ 2 * (A ^ 2 + B ^ 2 + D ^ 2) ∧
      g ^ 3 - 27 * h ^ 2 = 16 * P ^ 6 * (A * B * D) ^ 2 := by
  have a12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h12) (by linear_combination r1 - r2)
  have a13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h13) (by linear_combination r1 - r3)
  have s : e1 + e2 + e3 = 0 := by
    have : (e2 - e3) * (e1 + e2 + e3) = (e2 - e3) * 0 := by linear_combination (a12 - a13) / 4
    exact mul_left_cancel₀ (sub_ne_zero.2 h23) this
  have hh : h = 4 * e1 ^ 3 - g * e1 := by linear_combination -r1
  have k1 : (P * A) ^ 2 = (e1 - e2) ^ 2 := by rw [d1]
  have k2 : (P * B) ^ 2 = (e1 - e3) ^ 2 := by rw [d2]
  have k3 : (P * D) ^ 2 = (e3 - e2) ^ 2 := by rw [d3]
  obtain rfl : e3 = -e1 - e2 := by linear_combination s
  subst hh
  subst a12
  constructor
  · linear_combination (-2 / 3 : ℂ) * (k1 + k2 + k3)
  · have : 16 * P ^ 6 * (A * B * D) ^ 2 = 16 * ((P * A) ^ 2 * (P * B) ^ 2 * (P * D) ^ 2) := by ring
    rw [this, k1, k2, k3]
    ring
end GlobalTheory.WeberCubicAlgebra
