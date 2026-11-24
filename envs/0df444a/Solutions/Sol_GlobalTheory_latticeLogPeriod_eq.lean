-- Prove2me | solution 1 for GlobalTheory.latticeLogPeriod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:01.623725+00:00
-- url     : https://prove2.me/submissions/7450aefa-d4fd-47e8-9add-3d94c479993a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_covolume_lattice_eq
import Theorems.Thm_GlobalTheory_log_norm_lattice_discriminant

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
    latticeLogPeriod L = Real.log (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) := by
  have h1 := norm_ne_zero_iff.2 (ModularForm.eta_ne_zero τ.2)
  have h2 := norm_ne_zero_iff.2 ha
  have hy := τ.im_pos
  rw [latticeLogPeriod, covolume_lattice_eq ha h, log_norm_lattice_discriminant ha h,
    show (4 : ℝ) = 2 ^ 2 by norm_num]
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow]
  push_cast
  ring
end GlobalTheory
