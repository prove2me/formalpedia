-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41JointDenseSlopeV16
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:13:29.683884+00:00
-- url     : https://prove2.me/submissions/a17de77d-f751-4ad6-aa7b-767f2bc0a876

import Mathlib
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_Kyprianou_Ch04_exercise41OriginSlopeAEV13
import Theorems.Thm_Kyprianou_Ch04_exercise41CountableSlopeTransferV13
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (q : ℕ → NNReal) :
    ∀ᵐ w ∂P, ∀ᵐ s ∂(volume : Measure ℝ), ∃ n : ℕ, ∀ k : ℕ,
      0 < q k → q k < 1 / ((n : NNReal) + 1) →
      L.drift / 2 * (q k : ℝ) ≤ L.X (s.toNNReal + q k) w - L.X s.toNNReal w := by
  letI : IsProbabilityMeasure P := L.isProbability
  let G : Set (ℝ × Ω) := {p | ∃ n : ℕ, ∀ k : ℕ, 0 < q k →
    q k < 1 / ((n : NNReal) + 1) →
    L.drift / 2 * (q k : ℝ) ≤ L.X (p.1.toNNReal + q k) p.2 - L.X p.1.toNNReal p.2}
  have hx := rightContinuous_measurable_sections_joint_evaluation L.X
    (fun t => (L.adapted t).mono (F.le t) le_rfl) L.rightCont
  have hJ (k : ℕ) : Measurable (fun p : ℝ × Ω =>
      L.X (p.1.toNNReal + q k) p.2 - L.X p.1.toNNReal p.2) :=
    (hx.comp (((measurable_real_toNNReal.comp measurable_fst).add measurable_const).prodMk measurable_snd)).sub
      (hx.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  have hm : MeasurableSet G := by
    have he : G = (⋃ n : ℕ, ⋂ k : ℕ, ⋂ (_ : 0 < q k),
        ⋂ (_ : q k < 1 / ((n : NNReal) + 1)),
        {p : ℝ × Ω | L.drift / 2 * (q k : ℝ) ≤
          L.X (p.1.toNNReal + q k) p.2 - L.X p.1.toNNReal p.2}) := by
      ext p
      simp [G]
    rw [he]
    exact MeasurableSet.iUnion (fun n => MeasurableSet.iInter (fun k =>
      MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
        measurableSet_le measurable_const (hJ k)))))
  have horig : ∀ᵐ w ∂P, ∃ n : ℕ, ∀ k : ℕ, 0 < q k →
      q k < 1 / ((n : NNReal) + 1) → L.drift / 2 * (q k : ℝ) ≤ L.X (q k) w := by
    filter_upwards [exercise41OriginSlopeAEV13 P F L hBV hd] with w hw
    obtain ⟨n,hn⟩ := hw
    exact ⟨n,fun k hk hkn => hn (q k) hk hkn.le⟩
  have hfix (s : ℝ) : ∀ᵐ w ∂P, (s,w) ∈ G :=
    exercise41CountableSlopeTransferV13 P F L (fun _ => s.toNNReal)
      (fun t => @MeasurableSet.const Ω (F.rightCont t) (s.toNNReal ≤ t))
      q (L.drift / 2) horig
  exact (Measure.ae_ae_comm (μ := (volume : Measure ℝ)) (ν := P) hm).mp
    (Eventually.of_forall hfix)
