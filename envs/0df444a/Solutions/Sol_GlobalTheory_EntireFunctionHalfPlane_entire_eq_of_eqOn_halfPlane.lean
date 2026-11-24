-- Prove2me | solution 1 for GlobalTheory.EntireFunctionHalfPlane.entire_eq_of_eqOn_halfPlane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:26:26.786094+00:00
-- url     : https://prove2.me/submissions/cc4979e1-5a90-45dc-ae72-a362bdebaa1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EntireFunctionHalfPlane
open Filter Topology
namespace GlobalTheory.EntireFunctionHalfPlane
theorem _root_.solution {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (a : ℝ) (h : ∀ s : ℂ, a < s.re → f s = g s) : f = g := by
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hopen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((a + 1 : ℝ) : ℂ) ∈ {s : ℂ | a < s.re} := by
    simp
  have hev : f =ᶠ[𝓝 ((a + 1 : ℝ) : ℂ)] g :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem) (fun s hs => h s hs)
  exact AnalyticOnNhd.eq_of_eventuallyEq hf' hg' hev
end GlobalTheory.EntireFunctionHalfPlane
