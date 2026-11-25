-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.derivAdd_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:56:35.64136+00:00
-- url     : https://prove2.me/submissions/1f0bbe30-2350-4e62-8b7e-23ec1b422610

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
theorem _root_.solution (x₁ x₂ y₁ y₂ g₂ g₃ : ℂ) (hD : x₁ - x₂ ≠ 0)
    (E₁ : y₁ ^ 2 = 4 * x₁ ^ 3 - g₂ * x₁ - g₃) (E₂ : y₂ ^ 2 = 4 * x₂ ^ 3 - g₂ * x₂ - g₃) :
    2 * ((y₁ - y₂) / (x₁ - x₂)) *
        (((6 * x₁ ^ 2 - g₂ / 2) * (x₁ - x₂) - (y₁ - y₂) * y₁) / (x₁ - x₂) ^ 2) / 4 - y₁ =
      -((y₁ - y₂) / (x₁ - x₂) * (((y₁ - y₂) / (x₁ - x₂)) ^ 2 / 4 - x₁ - x₂ - x₁) + y₁) := by
  rw [← sub_eq_zero]
  have key : 2 * ((y₁ - y₂) / (x₁ - x₂)) *
        (((6 * x₁ ^ 2 - g₂ / 2) * (x₁ - x₂) - (y₁ - y₂) * y₁) / (x₁ - x₂) ^ 2) / 4 - y₁ -
      -((y₁ - y₂) / (x₁ - x₂) * (((y₁ - y₂) / (x₁ - x₂)) ^ 2 / 4 - x₁ - x₂ - x₁) + y₁) =
      (y₁ - y₂) / (4 * (x₁ - x₂) ^ 3) *
        ((y₂ ^ 2 - (4 * x₂ ^ 3 - g₂ * x₂ - g₃)) - (y₁ ^ 2 - (4 * x₁ ^ 3 - g₂ * x₁ - g₃))) := by
    field_simp
    ring
  rw [key, E₁, E₂]
  ring
end GroundTheory.Global.Elliptic
