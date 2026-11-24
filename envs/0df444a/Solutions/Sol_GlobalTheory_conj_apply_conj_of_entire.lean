-- Prove2me | solution 1 for GlobalTheory.conj_apply_conj_of_entire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:49.213127+00:00
-- url     : https://prove2.me/submissions/13308a02-61bb-4823-a7a0-adbe8200d9da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EulerProductNeZeroOneOfEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZetaEulerProductNeZeroOneAddMulI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (Z : ℂ → ℂ) (hZ : Differentiable ℂ Z)
    (h : ∀ s : ℂ, 1 < s.re → starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s) (s : ℂ) :
    starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by
  have hZ' : Differentiable ℂ (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) := by
    intro s
    have := (hZ (starRingEnd ℂ s)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have hev : (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) =ᶠ[nhds (2 : ℂ)] Z := by
    have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
    exact h s hs
  have := AnalyticOnNhd.eq_of_eventuallyEq
    (hZ'.differentiableOn.analyticOnNhd isOpen_univ)
    (hZ.differentiableOn.analyticOnNhd isOpen_univ) hev
  exact congrFun this s
end GlobalTheory
