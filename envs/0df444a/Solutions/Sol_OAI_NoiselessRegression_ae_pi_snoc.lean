-- Prove2me | solution 1 for OAI.NoiselessRegression.ae_pi_snoc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:30:08.228517+00:00
-- url     : https://prove2.me/submissions/75545c76-7a2f-47b6-a89e-46f720abb920

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
theorem solution {P : (Fin (n+1) → E) → Prop} (hP : MeasurableSet {v | P v}) :
    (∀ᵐ v ∂Measure.pi (fun _ => ν), P v) ↔
      ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν), ∀ᵐ x ∂ν, P (Fin.snoc v x) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) (Fin.last n)
  have hmp : MeasurePreserving e (Measure.pi (fun _ => ν)) (ν.prod (Measure.pi (fun _ : Fin n => ν))) :=
    measurePreserving_piFinSuccAbove (fun _ => ν) (Fin.last n)
  have hsymm : ∀ q : E × (Fin n → E), e.symm q = Fin.snoc q.2 q.1 := by
    rintro ⟨x, v⟩
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
  have hQ : MeasurableSet {q : E × (Fin n → E) | P (Fin.snoc q.2 q.1)} := by
    have := hP.preimage e.symm.measurable
    convert this using 1
    ext q; simp [hsymm]
  rw [← hmp.symm.map_eq, ae_map_iff e.symm.measurable.aemeasurable hP]
  simp only [hsymm]
  rw [Measure.ae_prod_iff_ae_ae hQ]
  exact Measure.ae_ae_comm (p := fun x v => P (Fin.snoc v x)) hQ

