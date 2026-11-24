-- Prove2me | solution 1 for GlobalTheory.eventually_mixedExpUnit_mixedLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:03.574252+00:00
-- url     : https://prove2.me/submissions/8a463713-5bfe-4412-9b2c-8da2158c98db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar

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
open Filter Topology
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] [NumberField K] :
    ∀ᶠ x in 𝓝 (1 : mixedSpace K), (mixedExpUnit K (mixedLog K x) : mixedSpace K) = x := by
  have h1 : ∀ᶠ x in 𝓝 (1 : mixedSpace K), ∀ w, 0 < x.1 w := by
    refine eventually_all.mpr fun w => ?_
    have hc : Continuous (fun x : mixedSpace K => x.1 w) := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simp))
  have h2 : ∀ᶠ x in 𝓝 (1 : mixedSpace K), ∀ w, x.2 w ≠ 0 := by
    refine eventually_all.mpr fun w => ?_
    have hc : Continuous (fun x : mixedSpace K => x.2 w) := by fun_prop
    exact hc.continuousAt.eventually_ne (by simp)
  filter_upwards [h1, h2] with x hx1 hx2
  exact Prod.ext (funext fun w => Real.exp_log (hx1 w)) (funext fun w => Complex.exp_log (hx2 w))
end GlobalTheory
