-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.add_add_eq_zero_of_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:54:44.914171+00:00
-- url     : https://prove2.me/submissions/b7c63284-429d-4fe0-a6aa-ba27d215ce13

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {g₂ g₃ x₁ x₂ x₃ : ℂ} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃)
    (h23 : x₂ ≠ x₃) (f1 : 4 * x₁ ^ 3 - g₂ * x₁ - g₃ = 0) (f2 : 4 * x₂ ^ 3 - g₂ * x₂ - g₃ = 0)
    (f3 : 4 * x₃ ^ 3 - g₂ * x₃ - g₃ = 0) : x₁ + x₂ + x₃ = 0 := by
  have s12 : 4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) = g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 h12) (by linear_combination f1 - f2)
  have s13 : 4 * (x₁ ^ 2 + x₁ * x₃ + x₃ ^ 2) = g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 h13) (by linear_combination f1 - f3)
  exact mul_left_cancel₀ (sub_ne_zero.2 h23) (by linear_combination (s12 - s13) / 4)
end GroundTheory.Global.Elliptic
