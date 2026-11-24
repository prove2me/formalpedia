-- Prove2me | solution 1 for GlobalTheory.bichar_deriv_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:19.120969+00:00
-- url     : https://prove2.me/submissions/674bafa4-a0b0-437d-9ab2-367c01514102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharDerivContDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory
open intervalIntegral Filter Topology
namespace GlobalTheory
theorem _root_.solution (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ)
    (hQ : Continuous (Function.uncurry Q))
    (hs : ∀ t s s', Q t (s + s') = Q t s * Q t s')
    (ht : ∀ t t' s, Q (t + t') s = Q t s * Q t' s)
    (h0 : ∀ t, Q t 0 = 1) :
    ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := by
  have hQt : ∀ t, Continuous (Q t) := fun t =>
    hQ.comp (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (t, s))
  set g : (Fin k → ℝ) → ℝ → ℂ := fun t δ => ∫ r in (0:ℝ)..δ, Q t r with hgdef
  have hg : ∀ t x, HasDerivAt (g t) (Q t x) x := fun t x =>
    ((hQt t).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hid : ∀ t s δ, Q t s * g t δ = g t (s + δ) - g t s := by
    intro t s δ
    have hint : ∀ a b : ℝ, IntervalIntegrable (Q t) MeasureTheory.volume a b :=
      fun a b => (hQt t).intervalIntegrable a b
    simp only [hgdef]
    rw [integral_interval_sub_left (hint _ _) (hint _ _)]
    have h1 : ∫ x in (0:ℝ)..δ, Q t (x + s) = ∫ x in s..s + δ, Q t x := by
      rw [intervalIntegral.integral_comp_add_right (fun x => Q t x) s]
      simp [add_comm]
    rw [← h1]
    simp_rw [hs, intervalIntegral.integral_mul_const]
    ring
  have hder : ∀ t δ, g t δ ≠ 0 → ∀ s,
      HasDerivAt (Q t) ((Q t (s + δ) - Q t s) / g t δ) s := by
    intro t δ hδ s
    have heq : Q t = fun u => (g t (u + δ) - g t u) / g t δ := by
      funext u; rw [← hid t u δ, mul_div_cancel_right₀ _ hδ]
    have ha : HasDerivAt (fun u => g t (u + δ)) (Q t (s + δ)) s :=
      HasDerivAt.comp_add_const s δ (hg t (s + δ))
    have h1 : HasDerivAt (fun u => (g t (u + δ) - g t u) / g t δ)
        ((Q t (s + δ) - Q t s) / g t δ) s := (ha.sub (hg t s)).div_const _
    rwa [← heq] at h1
  have hex : ∀ t, ∃ δ, g t δ ≠ 0 := by
    intro t
    have h := (hg t 0).eventually_ne (c := 0) (by rw [h0]; exact one_ne_zero)
    obtain ⟨z, hz⟩ := h.exists
    refine ⟨z, ?_⟩
    simpa [hgdef] using hz
  have hd : ∀ t, HasDerivAt (Q t) (deriv (Q t) 0) 0 := by
    intro t
    obtain ⟨δ, hδ⟩ := hex t
    exact (hder t δ hδ 0).differentiableAt.hasDerivAt
  have hadd : ∀ t t', deriv (Q (t + t')) 0 = deriv (Q t) 0 + deriv (Q t') 0 := by
    intro t t'
    have e : Q (t + t') = Q t * Q t' := funext fun s => by rw [Pi.mul_apply, ht]
    have hm := (hd t).mul (hd t')
    rw [← e] at hm
    rw [hm.deriv, h0, h0]; ring
  let c : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun t => deriv (Q t) 0) hadd
  have hQ0 : ∀ s, Q 0 s = 1 := by
    intro s
    have h1 : Q 0 s = Q 0 s * Q 0 s := by simpa using ht 0 0 s
    have h2 : Q 0 s * Q 0 (-s) = 1 := by rw [← hs, add_neg_cancel, h0]
    have hne : Q 0 s ≠ 0 := left_ne_zero_of_mul_eq_one h2
    have := mul_left_cancel₀ hne (h1.symm.trans (mul_one _).symm)
    exact this
  have hgc : Continuous fun t => g t 1 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hQ 0 1
  have hg01 : g 0 1 = 1 := by simp [hgdef, hQ0]
  have hne : ∀ᶠ t in 𝓝 (0 : Fin k → ℝ), g t 1 ≠ 0 :=
    hgc.continuousAt.eventually_ne (by rw [hg01]; exact one_ne_zero)
  have hc0 : ContinuousAt c 0 := by
    have hQ1 : Continuous fun t => Q t 1 :=
      hQ.comp (continuous_id.prodMk continuous_const : Continuous fun t => (t, (1:ℝ)))
    have hf : ContinuousAt (fun t => (Q t 1 - 1) / g t 1) 0 :=
      ((hQ1.sub continuous_const).continuousAt).div hgc.continuousAt (by rw [hg01]; exact one_ne_zero)
    refine hf.congr ?_
    filter_upwards [hne] with t htne
    have := (hder t 1 htne 0).deriv
    simp only [zero_add, h0] at this
    simp [c, this]
  have hcc : Continuous c := continuous_of_continuousAt_zero c hc0
  have : (fun t => deriv (Q t) 0) = ⇑(c.toRealLinearMap hcc) := by
    funext t; simp [c]
  rw [this]
  exact (c.toRealLinearMap hcc).contDiff
end GlobalTheory
