-- Prove2me | solution 1 for GlobalTheory.LocalNorm.exists_eq_sq_add_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:03.137955+00:00
-- url     : https://prove2.me/submissions/e6365a13-1275-4910-9b58-f60981e56567

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm
namespace GlobalTheory.LocalNorm
theorem _root_.solution {K : Type*} [Field K] {d x a₀ b₀ a₁ b₁ a₂ b₂ : K}
    (h₁ : a₁ ^ 2 + d * b₁ ^ 2 ≠ 0)
    (h : x * (a₁ ^ 2 + d * b₁ ^ 2) = (a₀ ^ 2 + d * b₀ ^ 2) * (a₂ ^ 2 + d * b₂ ^ 2)) :
    ∃ a b, x = a ^ 2 + d * b ^ 2 := by
  refine ⟨((a₀ * a₂ - d * b₀ * b₂) * a₁ - d * (a₀ * b₂ + a₂ * b₀) * b₁) / (a₁ ^ 2 + d * b₁ ^ 2),
    ((a₀ * a₂ - d * b₀ * b₂) * b₁ + (a₀ * b₂ + a₂ * b₀) * a₁) / (a₁ ^ 2 + d * b₁ ^ 2), ?_⟩
  field_simp
  linear_combination (a₁ ^ 2 + d * b₁ ^ 2) * h
end GlobalTheory.LocalNorm
