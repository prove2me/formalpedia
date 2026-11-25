-- Prove2me | solution 1 for GlobalTheory.CharFormDeriv.charForm_kills_linear_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:30:24.205949+00:00
-- url     : https://prove2.me/submissions/ebbf8fe8-8dd5-4bd4-a46f-1bc7c756de2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Theorems.Thm_GlobalTheory_CharFormDeriv_hasTemperateGrowth_char
import Theorems.Thm_GlobalTheory_CharFormDeriv_seminorm_rem_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv
namespace GlobalTheory.CharFormDeriv
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (T : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (f g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * f x) → T g = 0 := by
  intro V _ _ _ T hT L f g hg
  let ft : ℝ → SchwartzMap V ℂ := fun t =>
    SchwartzMap.smulLeftCLM ℂ (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) f
  have hft : ∀ t x, ft t x = Complex.exp ((I * t) * (L x : ℂ)) * f x := fun t x => by
    simp only [ft, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_char L t), smul_eq_mul]
  have hTft : ∀ t : ℝ, T (ft t) = T f := fun t => hT (t • L) f (ft t) (fun x => by
    rw [hft, ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc])
  let u : ℝ → SchwartzMap V ℂ := fun t => (t : ℂ)⁻¹ • (ft t - f) - I • g
  have hu : ∀ t : ℝ, ∀ x, u t x = rem t (L x) * f x := fun t x => by
    simp only [u, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hft, hg, rem, smul_eq_mul]
    ring
  have hTu : ∀ t : ℝ, T (u t) = -I * T g := fun t => by
    simp only [u, map_sub, map_smul, hTft, sub_self, smul_zero, smul_eq_mul, zero_sub]
    ring
  have hlim : Filter.Tendsto u (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds u 0]
    rintro ⟨k, n⟩ ε hε
    set K := 3 * 2 ^ n * (1 + ‖L‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)
      with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) (mul_nonneg (by positivity) (apply_nonneg _ _))
    have hδ : 0 < min 1 (ε / (K + 1)) := lt_min one_pos (div_pos hε (by linarith))
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ), self_mem_nhdsWithin]
      with t ht ht0
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have ht0' : t ≠ 0 := ht0
    have ht1 : |t| ≤ 1 := (lt_of_lt_of_le ht (min_le_left _ _)).le
    have htε : |t| < ε / (K + 1) := lt_of_lt_of_le ht (min_le_right _ _)
    rw [sub_zero]
    show SchwartzMap.seminorm ℂ k n (u t) < ε
    calc SchwartzMap.seminorm ℂ k n (u t) ≤ |t| * K := seminorm_rem_mul_le L f (u t) ht0' ht1 (hu t) k n
      _ ≤ |t| * (K + 1) := by gcongr; linarith
      _ < ε / (K + 1) * (K + 1) := by gcongr
      _ = ε := by field_simp
  have hcont : Filter.Tendsto (fun t => T (u t)) (nhdsWithin 0 {0}ᶜ) (nhds (T 0)) :=
    (T.continuous.tendsto 0).comp hlim
  have hconst : Filter.Tendsto (fun t => T (u t)) (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (-I * T g)) := by
    simp only [hTu]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hconst hcont
  rw [map_zero, neg_mul, neg_eq_zero] at heq
  exact (mul_eq_zero.mp heq).resolve_left Complex.I_ne_zero
end GlobalTheory.CharFormDeriv
