-- Prove2me | solution 1 for GlobalTheory.TorusElliptic.symbol_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:07.187836+00:00
-- url     : https://prove2.me/submissions/be48e2c9-8bf6-42c5-bd80-595c7b7f4f65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.TorusElliptic
namespace GlobalTheory.TorusElliptic
theorem _root_.solution {n m : ℕ} (p : Fin m → Fin n → ℂ)
    (hp : ∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Fin n → ℤ, ν ≠ 0 → ∃ a, ε ≤ ‖∑ k, p a k * (ν k : ℂ)‖ := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ) :=
    { toFun := fun ξ a => ∑ k, p a k * (ξ k : ℂ)
      map_add' := fun ξ η => by
        funext a; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r ξ => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]
        push_cast
        exact Finset.sum_congr rfl fun k _ => by ring }
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ξ hξ
    exact hp ξ fun a => congrFun hξ a
  obtain ⟨K, hK, hA⟩ := L.exists_antilipschitzWith hL
  have hK' : (0 : ℝ) < K := hK
  refine ⟨1 / K, by positivity, fun ν hν => ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 : ‖L (fun k => (ν k : ℝ))‖ < 1 / K := by
    rw [pi_norm_lt_iff (by positivity)]
    intro a
    simpa [L] using hcon a
  have h2 := hA.le_mul_dist (fun k => (ν k : ℝ)) 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h2
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hν
  have h3 : (1 : ℝ) ≤ ‖(fun k => (ν k : ℝ))‖ := by
    refine le_trans ?_ (norm_le_pi_norm (fun k => (ν k : ℝ)) k)
    rw [Real.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hk
  rw [lt_div_iff₀ hK'] at h1
  linarith
end GlobalTheory.TorusElliptic
