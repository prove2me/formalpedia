-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolFamily.continuousOn_deriv_param
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:00.635825+00:00
-- url     : https://prove2.me/submissions/7f28e4b6-faa4-4128-ba01-641dbfe6cd89

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AutomorphicFunctionalHolomorphicDerivative
import Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_continuousOn_deriv_family


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolFamily
namespace GlobalTheory.CompanionTheory.HolFamily
theorem _root_.solution {G : Type} [TopologicalSpace G] {U : Set ℂ} (hU : IsOpen U)
    {E : ℂ → G → ℂ} (hd : ∀ g, DifferentiableOn ℂ (E · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ)) :
    ContinuousOn (fun y : ℂ × G => deriv (E · y.2) y.1) (U ×ˢ Set.univ) := by
  have hc' : ContinuousOn (fun q : G × ℂ => E q.2 q.1) (Set.univ ×ˢ U) :=
    hc.comp continuous_swap.continuousOn fun q hq => ⟨hq.2, Set.mem_univ _⟩
  have h := continuousOn_deriv_family G U hU (fun g z => E z g) hc' hd
  exact h.comp continuous_swap.continuousOn fun y hy => ⟨Set.mem_univ _, hy.1⟩
end GlobalTheory.CompanionTheory.HolFamily
