-- Prove2me | solution 1 for Kyprianou.Ch01.randomWalkIID_reversal_jointLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T17:16:37.948612+00:00
-- url     : https://prove2.me/submissions/8bbca7ad-9727-41d7-8909-4f1b19c6053f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

/-- A finite iid vector and its reversed vector both have the same product law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hindep : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hLaw : ∀ i : ℕ, HasLaw (increment i) jumpLaw P)
    (n : ℕ) :
    P.map (fun ω => fun i : Fin n => increment i ω) =
      P.map (fun ω => fun i : Fin n => increment (Fin.rev i) ω) := by
  have hfirst :
      iIndepFun (fun i : Fin n => increment (i : ℕ)) P :=
    hindep.precomp Fin.val_injective
  have hrev :
      iIndepFun (fun i : Fin n => increment (Fin.rev i : ℕ)) P :=
    hindep.precomp (Fin.val_injective.comp Fin.rev_injective)
  have hfirstLaw :
      HasLaw (fun ω => fun i : Fin n => increment i ω)
        (Measure.pi (fun _ : Fin n => jumpLaw)) P :=
    iIndepFun.hasLaw_pi (fun i : Fin n => hLaw i) hfirst
  have hrevLaw :
      HasLaw (fun ω => fun i : Fin n => increment (Fin.rev i) ω)
        (Measure.pi (fun _ : Fin n => jumpLaw)) P :=
    iIndepFun.hasLaw_pi (fun i : Fin n => hLaw (Fin.rev i)) hrev
  exact hfirstLaw.map_eq.trans hrevLaw.map_eq.symm
