-- Prove2me | solution 1 for Kyprianou.Ch02.independentAeCutoffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:00:41.921373+00:00
-- url     : https://prove2.me/submissions/74eea654-20d7-45a4-a45f-1498153dd972

import Mathlib.Probability.Independence.Basic
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ι → Prop) [DecidablePred H] (X Y : ι → Ω → ENNReal)
    (hX : iIndepFun X P)
    (hEq : ∀ i, Y i =ᵐ[P] (fun ω => if H i then X i ω else ⊤)) :
    iIndepFun Y P := by
  classical
  have hm : ∀ i, Measurable (fun x : ENNReal => if H i then x else ⊤) := by
    intro i
    by_cases hi : H i
    · simp only [if_pos hi]
      exact measurable_id
    · simpa [hi] using (measurable_const : Measurable (fun _ : ENNReal => (⊤ : ENNReal)))
  have hmap : iIndepFun (fun i ω => if H i then X i ω else ⊤) P := by
    simpa only [Function.comp_def] using
      hX.comp (fun i x => if H i then x else ⊤) hm
  exact (iIndepFun_congr hEq).2 hmap
