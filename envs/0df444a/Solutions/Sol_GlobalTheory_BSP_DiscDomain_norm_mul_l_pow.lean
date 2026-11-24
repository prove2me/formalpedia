-- Prove2me | solution 1 for GlobalTheory.BSP.DiscDomain.norm_mul_l_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:05.91103+00:00
-- url     : https://prove2.me/submissions/f45bdd4b-a3ac-4be5-acfc-ce75e5051e35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsDomainClosedDiscGaugeCompletionOfEquivNorm
import Theorems.Thm_GlobalTheory_BSP_DiscDomain_norm_mul_l

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.BSP GlobalTheory.BSP.DiscDomain
variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0}
namespace GlobalTheory.BSP.DiscDomain
theorem _root_.solution (n : ℕ) (y : PreDisc l u ρ) :
    ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ n‖ * (l : ℝ) ^ n = ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := norm_mul_l (y * algebraMap A (PreDisc l u ρ) (l : A) ^ n)
    calc ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ (n + 1)‖ * (l : ℝ) ^ (n + 1)
        = ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ n * algebraMap A (PreDisc l u ρ) (l : A)‖ * l
            * (l : ℝ) ^ n := by
          rw [pow_succ, pow_succ, mul_assoc y]; ring
      _ = ‖y‖ := by rw [h, ih]
end GlobalTheory.BSP.DiscDomain
