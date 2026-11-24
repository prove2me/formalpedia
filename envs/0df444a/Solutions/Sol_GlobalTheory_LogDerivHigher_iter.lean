-- Prove2me | solution 1 for GlobalTheory.LogDerivHigher.iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:24.534942+00:00
-- url     : https://prove2.me/submissions/6b8771cf-2e14-4a91-a0bb-ac886b522b85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Theorems.Thm_GlobalTheory_LogDerivHigher_hasDerivAt_pole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.LogDerivHigher
namespace GlobalTheory.LogDerivHigher
theorem _root_.solution (f : ℕ → ℂ) (hf : LSeries.abscissaOfAbsConv f ≤ 1) (e : ℂ) (Z : Finset ℂ) (m : ℂ → ℂ)
    (hZ : ∀ w ∈ Z, w.re ≤ 1) (g : ℂ → ℂ)
    (hg : ∀ s : ℂ, 1 < s.re → g s = -(LSeries f s - e / (s - 1) + ∑ w ∈ Z, m w / (s - w)))
    (k : ℕ) : ∀ s : ℂ, 1 < s.re → iteratedDeriv k g s = (-1) ^ (k + 1) *
      (LSeries (LSeries.logMul^[k] f) s + k.factorial *
        (- (e / (s - 1) ^ (k + 1)) + ∑ w ∈ Z, m w / (s - w) ^ (k + 1))) := by
  induction k with
  | zero => intro s hs; simp [hg s hs]; ring
  | succ k ih =>
    intro s hs
    have hev : iteratedDeriv k g =ᶠ[𝓝 s] fun s => (-1) ^ (k + 1) *
      (LSeries (LSeries.logMul^[k] f) s + k.factorial *
        (- (e / (s - 1) ^ (k + 1)) + ∑ w ∈ Z, m w / (s - w) ^ (k + 1))) := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
      exact ih z hz
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have a1 : LSeries.abscissaOfAbsConv (LSeries.logMul^[k] f) < s.re := by
      rw [LSeries.absicssaOfAbsConv_logPowMul]
      exact hf.trans_lt (by exact_mod_cast hs)
    have d1 := LSeries_hasDerivAt a1
    have d2 := hasDerivAt_pole e 1 s k (by rintro rfl; simp at hs)
    have d3 := HasDerivAt.fun_sum (u := Z) fun w hw => hasDerivAt_pole (m w) w s k
      (by rintro rfl; linarith [hZ _ hw])
    have d4 := (d1.fun_add ((d2.fun_neg.fun_add d3).const_mul (k.factorial : ℂ))).const_mul
      ((-1 : ℂ) ^ (k + 1))
    rw [d4.deriv, Function.iterate_succ', ← Finset.mul_sum, Nat.factorial_succ]
    simp only [Function.comp_apply]
    push_cast
    ring
end GlobalTheory.LogDerivHigher
