-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.linearIndependent_functionals_dualFamily
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:12:55.497396+00:00
-- url     : https://prove2.me/submissions/168cce1f-b6cf-456d-82a6-04c38d58e8f6

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_evaluationMap_surjective

theorem solution
    {K V ι : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [AddCommGroup V] [Module K V]
    (L : ι → V →ₗ[K] K) (hL : LinearIndependent K L) :
    ∃ q : ι → V, ∀ x y, L x (q y) = if x = y then 1 else 0 := by
  classical
  let E := evaluationMap L
  have hE : Function.Surjective E := by
    exact OAI.PiExponent.LogarithmicJetIdeals.evaluationMap_surjective L hL
  refine ⟨fun y => Classical.choose (hE (fun x => if x = y then 1 else 0)), ?_⟩
  intro x y
  have hq := Classical.choose_spec (hE (fun z => if z = y then 1 else 0))
  have hx := congrFun hq x
  simpa [E, evaluationMap] using hx