-- Prove2me | solution 1 for GlobalTheory.MultilinFubini.aestronglyMeasurable_pi_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:04:29.579272+00:00
-- url     : https://prove2.me/submissions/ff6ac7d1-51d1-4ab0-9e0c-bf42587e35c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralContinuousMultilinearMapPiMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.MultilinFubini
namespace GlobalTheory.MultilinFubini
theorem _root_.solution {α : Type*} {m0 : MeasurableSpace α} {ν : Measure α}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {f : ∀ i, α → E i} (hf : ∀ i, AEStronglyMeasurable (f i) ν) :
    AEStronglyMeasurable (fun x i => f i x) ν := by
  have key : ∀ s : Finset ι,
      AEStronglyMeasurable (fun x (i : ι) => if i ∈ s then f i x else 0) ν := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, if_false]; exact aestronglyMeasurable_const
    | insert a s ha ih =>
      have hc : Continuous (fun p : E a × (∀ i, E i) => Function.update p.2 a p.1) :=
        continuous_snd.update a continuous_fst
      refine (hc.comp_aestronglyMeasurable ((hf a).prodMk ih)).congr (ae_of_all _ fun x => ?_)
      funext i
      by_cases hi : i = a
      · subst hi; simp
      · simp [Function.update_of_ne hi, hi]
  simpa using key Finset.univ
end GlobalTheory.MultilinFubini
