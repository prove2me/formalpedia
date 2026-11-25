-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ParSmooth.contDiff_integral_comp_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:13:05.784689+00:00
-- url     : https://prove2.me/submissions/f02729c6-8fde-43ea-91d8-8bf77e2ccc6d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_JetProofs_ContinuousIteratedFDerivPartial
import Theorems.Thm_GlobalTheory_CompanionTheory_ParSmooth_continuous_iteratedFDeriv_partial
import Theorems.Thm_GroundTheory_Automorphic_contDiff_integral_of_iteratedFDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ParSmooth
namespace GlobalTheory.CompanionTheory.ParSmooth
theorem _root_.solution {P Q E β : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace β] [T2Space β]
    [SecondCountableTopology β] [CompactSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν] (Ψ : P × Q → E) (hΨ : ContDiff ℝ ∞ Ψ) (q : β → Q)
    (hq : Continuous q) : ContDiff ℝ ∞ fun y => ∫ a, Ψ (y, q a) ∂ν := by
  refine GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv (μ := ν) (fun y a => Ψ (y, q a))
    (fun a => hΨ.comp (contDiff_id.prodMk contDiff_const)) (fun k => ?_)
    (fun _ => ⟨Set.univ, Filter.univ_mem, Set.univ, isCompact_univ,
      fun _ _ a ha => absurd (Set.mem_univ a) ha⟩)
  have h : Continuous fun p : P × β => (p.1, q p.2) :=
    continuous_fst.prodMk (hq.comp continuous_snd)
  exact (continuous_iteratedFDeriv_partial Ψ hΨ k).comp h
end GlobalTheory.CompanionTheory.ParSmooth
