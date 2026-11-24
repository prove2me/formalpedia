-- Prove2me | solution 1 for GlobalTheory.ConeImage.exists_continuous_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:43.04046+00:00
-- url     : https://prove2.me/submissions/4d4db68d-e910-4e6b-be18-af1ec37b96e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage
namespace GlobalTheory.ConeImage
theorem _root_.solution {σ : Type*} (p : Polynomial (MvPolynomial σ ℂ)) :
    ∃ k : (σ → ℂ) × ℂ × ℂ → ℂ, Continuous k ∧ ∀ u s s',
      p.eval₂ (MvPolynomial.eval u) s' - p.eval₂ (MvPolynomial.eval u) s
        = (s' - s) * k (u, s, s') ∧
      k (u, s, s) = p.derivative.eval₂ (MvPolynomial.eval u) s := by
  induction p using Polynomial.induction_on with
  | C a => exact ⟨0, continuous_zero, fun u s s' => by simp⟩
  | add p q hp hq =>
    obtain ⟨k, hk, h⟩ := hp
    obtain ⟨l, hl, h'⟩ := hq
    refine ⟨k + l, hk.add hl, fun u s s' => ⟨?_, ?_⟩⟩
    · simp only [Polynomial.eval₂_add, Pi.add_apply]
      linear_combination (h u s s').1 + (h' u s s').1
    · simp [Polynomial.eval₂_add, (h u s s').2, (h' u s s').2]
  | monomial n a hp =>
    obtain ⟨k, hk, h⟩ := hp
    refine ⟨fun x => k x * x.2.2 + MvPolynomial.eval x.1 a * x.2.1 ^ n, ?_, fun u s s' => ⟨?_, ?_⟩⟩
    · have := MvPolynomial.continuous_eval a
      fun_prop
    · have := (h u s s').1
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at this ⊢
      linear_combination s' * this
    · dsimp only
      rw [(h u s s).2, pow_succ, ← mul_assoc, Polynomial.derivative_mul]
      simp [Polynomial.eval₂_add, Polynomial.eval₂_mul]
end GlobalTheory.ConeImage
