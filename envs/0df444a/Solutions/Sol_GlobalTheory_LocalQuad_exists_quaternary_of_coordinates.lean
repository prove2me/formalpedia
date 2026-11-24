-- Prove2me | solution 1 for GlobalTheory.LocalQuad.exists_quaternary_of_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:49:05.924856+00:00
-- url     : https://prove2.me/submissions/d3886eea-69f6-4fe5-8512-50a7aa6b9afd

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
variable {k : Type*} [Field k]
namespace GlobalTheory.LocalQuad
theorem _root_.solution {α β γ : k} (hα : α ≠ 0) (hβ : β ≠ 0)
    {X₀ X₁ Y₀ Y₁ : k}
    (h1 : β = X₀ ^ 2 + α * β * γ * X₁ ^ 2 - α * (Y₀ ^ 2 + α * β * γ * Y₁ ^ 2))
    (h2 : X₀ * X₁ = α * (Y₀ * Y₁)) :
    ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - α * y ^ 2 - β * z ^ 2 + γ * t ^ 2 = 0 := by
  by_cases hw : X₁ ^ 2 - α * Y₁ ^ 2 = 0
  · exact ⟨X₀, Y₀, 1, 0, by simp, by linear_combination -h1 - α * β * γ * hw⟩
  · refine ⟨-Y₁ * (α * β), -X₁ * β, -(X₀ * Y₁ - Y₀ * X₁) * α, (X₁ ^ 2 - α * Y₁ ^ 2) * (α * β),
      Or.inr (Or.inr (Or.inr (mul_ne_zero hw (mul_ne_zero hα hβ)))), ?_⟩
    linear_combination (-(α * β * (X₁ ^ 2 - α * Y₁ ^ 2))) * h1 - α * β * (X₀ * X₁ - α * (Y₀ * Y₁)) * h2
end GlobalTheory.LocalQuad
