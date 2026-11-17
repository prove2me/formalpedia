-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_marginal_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:48:03.8787+00:00
-- url     : https://prove2.me/submissions/bcdd2551-921e-4557-b7c1-47beb6d6b214

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_aemeasurable_of_poisson_law
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_lintegral_nat_count
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : Omega -> Nat) (r : NNReal)
    (hX : P.map X = poissonMeasure r) :
    (∫⁻ w, ((X w : Nat) : ENNReal) ∂P) = (r : ENNReal) := by
  have hmeas : AEMeasurable X P :=
    aemeasurable_of_poisson_law P r X hX
  have hcast : Measurable (fun k : Nat => (k : ENNReal)) := by fun_prop
  have hmap := lintegral_map' hcast.aemeasurable hmeas
  have hidentity :
      (∫⁻ k : Nat, (k : ENNReal) ∂P.map X) =
      (∫⁻ w : Omega, ((X w : Nat) : ENNReal) ∂P) := by
    simpa only [Function.comp_def] using hmap
  rw [← hidentity, hX]
  exact poisson_lintegral_nat_count r
