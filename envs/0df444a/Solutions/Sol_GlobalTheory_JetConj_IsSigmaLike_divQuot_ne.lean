-- Prove2me | solution 1 for GlobalTheory.JetConj.IsSigmaLike.divQuot_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:17.639207+00:00
-- url     : https://prove2.me/submissions/acb4ec32-d58e-47c0-8c3f-f669070185f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
import Theorems.Thm_GlobalTheory_JetConj_eventually_add_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
variable {L : PeriodPair} {σ : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace IsSigmaLike
theorem _root_.solution (H : IsSigmaLike L σ) {u : ℂ} (hu : u ∉ L.lattice) {n : ℕ} (hn : n ≠ 0) :
    ¬ divQuot σ u n =ᶠ[𝓝 0] 0 := by
  intro h
  have hσ := H.diff
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have a : Differentiable ℂ fun z => σ (n * z + n * u) := by fun_prop
  have e : (fun z => σ (n * z + n * u)) =ᶠ[𝓝 0] 0 := by
    filter_upwards [h, eventually_add_notMem L (z := 0) (by simpa using hu)] with w hw hw'
    simpa [divQuot, mt (H.zero_iff _).1 hw'] using hw
  have e2 := (a.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ 0) e (Set.mem_univ (u / n - u))
  simp only [Pi.zero_apply] at e2
  rw [show (n : ℂ) * (u / n - u) + n * u = u by field_simp; ring] at e2
  exact hu ((H.zero_iff _).1 e2)
end IsSigmaLike
end GlobalTheory.JetConj
