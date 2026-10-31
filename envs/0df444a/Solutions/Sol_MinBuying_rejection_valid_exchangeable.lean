-- Prove2me | solution 1 for MinBuying.rejection_valid_exchangeable
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:55:08.868045+00:00
-- url     : https://prove2.me/submissions/c3c94ecd-34e4-4831-afff-a754d8f2ba6c

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory Set MinBuying
open scoped BigOperators ENNReal
noncomputable section

namespace MinBuyingRejectionSymmetryProof

private def liftPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun i := Fin.cases 0 (fun j => (σ j).succ) i
  invFun i := Fin.cases 0 (fun j => (σ.symm j).succ) i
  left_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> simp

private lemma measurable_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Measurable (permuteCoordinates σ) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (σ i))

private lemma cond_permute (n : ℕ) (μ : JointLaw (n+1)) (hex : Exchangeable μ)
    (a : ℝ) (σ : Equiv.Perm (Fin n)) :
    Measure.map (permuteCoordinates (liftPerm σ))
      (ProbabilityTheory.cond μ {v : Valuations (n+1) | v 0 < a}) =
      ProbabilityTheory.cond μ {v : Valuations (n+1) | v 0 < a} := by
  let B : Set (Valuations (n+1)) := {v | v 0 < a}
  have hB : MeasurableSet B := measurableSet_lt (measurable_pi_apply 0) measurable_const
  have hm := measurable_permute (liftPerm σ)
  ext T hT
  rw [Measure.map_apply hm hT,ProbabilityTheory.cond_apply' (hT.preimage hm),
    ProbabilityTheory.cond_apply' hT]
  have heq : B ∩ (permuteCoordinates (liftPerm σ) ⁻¹' T) =
      permuteCoordinates (liftPerm σ) ⁻¹' (B ∩ T) := by
    ext v
    simp [B,permuteCoordinates,liftPerm]
  change (μ B)⁻¹ * μ (B ∩ (permuteCoordinates (liftPerm σ) ⁻¹' T)) =
    (μ B)⁻¹ * μ (B ∩ T)
  rw [heq,← Measure.map_apply hm (hB.inter hT),hex (liftPerm σ)]

end MinBuyingRejectionSymmetryProof

theorem solution (n : ℕ) (μ : JointLaw (n+1)) (hμ : ValidLaw μ)
    (hex : Exchangeable μ) (a : ℝ)
    (hB : 0 < μ {v : Valuations (n+1) | v 0 < a}) :
    let ν : JointLaw n := Measure.map (fun v : Valuations (n+1) => fun i : Fin n => v i.succ)
      (ProbabilityTheory.cond μ {v : Valuations (n+1) | v 0 < a})
    ValidLaw ν ∧ Exchangeable ν := by
  classical
  let B : Set (Valuations (n+1)) := {v | v 0 < a}
  let tail : Valuations (n+1) → Valuations n := fun v i => v i.succ
  have htail : Measurable tail := measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)
  letI : IsProbabilityMeasure μ := hμ.1
  letI : IsProbabilityMeasure (ProbabilityTheory.cond μ B) :=
    ProbabilityTheory.cond_isProbabilityMeasure (ne_of_gt hB)
  constructor
  · constructor
    · exact Measure.isProbabilityMeasure_map htail.aemeasurable
    · apply (ae_map_iff htail.aemeasurable (by measurability)).mpr
      have hpos : ∀ᵐ v ∂ProbabilityTheory.cond μ B, ∀ i,0 ≤ v i :=
        Measure.ae_smul_measure (ae_restrict_of_ae hμ.2) _
      filter_upwards [hpos] with v hv
      exact fun i => hv i.succ
  · intro σ
    have hm := MinBuyingRejectionSymmetryProof.measurable_permute σ
    have hml := MinBuyingRejectionSymmetryProof.measurable_permute
      (MinBuyingRejectionSymmetryProof.liftPerm σ)
    have hcomm : permuteCoordinates σ ∘ tail =
        tail ∘ permuteCoordinates (MinBuyingRejectionSymmetryProof.liftPerm σ) := by
      funext v i
      simp [tail,permuteCoordinates,MinBuyingRejectionSymmetryProof.liftPerm]
    change Measure.map (permuteCoordinates σ) (Measure.map tail (ProbabilityTheory.cond μ B)) =
      Measure.map tail (ProbabilityTheory.cond μ B)
    rw [Measure.map_map hm htail,hcomm,← Measure.map_map htail hml]
    rw [MinBuyingRejectionSymmetryProof.cond_permute n μ hex a σ]
