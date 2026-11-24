-- Prove2me | solution 1 for GlobalTheory.log_norm_lattice_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:01.371305+00:00
-- url     : https://prove2.me/submissions/a2a2140f-3237-4b3b-a6ea-82c27ee88068

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    Real.log ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ = 12 * (Real.log (2 * π) - Real.log ‖a‖)
      + 24 * Real.log ‖ModularForm.eta τ‖ := by
  have h1 := norm_ne_zero_iff.2 (ModularForm.eta_ne_zero τ.2)
  have h2 := norm_ne_zero_iff.2 ha
  rw [← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h, ModularForm.discriminant, norm_mul,
    norm_pow, norm_pow, norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by simp [Real.pi_pos.le],
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div (by positivity) h2]
  norm_num
end GlobalTheory
