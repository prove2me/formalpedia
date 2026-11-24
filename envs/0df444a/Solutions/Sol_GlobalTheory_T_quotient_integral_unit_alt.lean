-- Prove2me | solution 1 for GlobalTheory.T.quotient_integral_unit_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:07.146745+00:00
-- url     : https://prove2.me/submissions/3c48e3d6-83a1-445b-9aa5-404328bb3e92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuotientIntegralUnit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuotientIntegralUnitStatement
import Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_quotient_integral_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N c b e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) → (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) → ‖u.det‖ = 1 → e₁ * e₁ = e₁ → e₂ * e₂ = e₂ → e₃ * e₃ = e₃ → e₁ * e₂ = 0 → e₁ * e₃ = 0 → e₂ * e₃ = 0 → e₁ + e₂ + e₃ = 1 → c * e₁ = u * e₁ → c * e₂ = ϖ • (a₂ * e₂) → c⁻¹ * e₃ = ϖ • (a₃ * e₃) → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit | exact GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit | (intros; apply GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit <;> assumption)
end _root_.GlobalTheory.T
