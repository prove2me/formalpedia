-- Prove2me | solution 1 for MeasureTheory.exists_holder_representative_of_ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T17:23:37.424221+00:00
-- url     : https://prove2.me/submissions/a95de80d-97ab-448b-a1d9-5abe3e48228c

import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

theorem solution {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    (K : ℝ≥0) (α : ℝ) (hα : 0 < α) (v : ℕ → X → Y) (f : X → Y)
    (hv : ∀ j x y, dist (v j x) (v j y) ≤ (K : ℝ) * dist x y ^ α)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun j => v j x) atTop (𝓝 (f x))) :
    ∃ u : X → Y, Continuous u ∧ u =ᵐ[μ] f ∧
      ∀ x y, dist (u x) (u y) ≤ (K : ℝ) * dist x y ^ α := by
  classical
  let s : Set X := {x | Tendsto (fun j => v j x) atTop (𝓝 (f x))}
  have hs : Dense s := μ.dense_of_ae hf
  have hbound (x : s) (y : s) :
      dist (f x) (f y) ≤ (K : ℝ) * dist (x : X) (y : X) ^ α :=
    le_of_tendsto (x.property.dist y.property) (Eventually.of_forall fun j => hv j x y)
  have hholder : HolderWith K ⟨α, hα.le⟩ (fun x : s => f x) := by
    intro x y
    rw [edist_dist, edist_dist]
    change ENNReal.ofReal (dist (f x) (f y)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (dist (x : X) (y : X)) ^ α
    rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le]
    simpa only [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      using ENNReal.ofReal_le_ofReal (hbound x y)
  have huc : UniformContinuous (fun x : s => f x) := hholder.uniformContinuous hα
  let u : X → Y := hs.extend (fun x : s => f x)
  have hu : Continuous u := (hs.uniformContinuous_extend huc).continuous
  have heq (x : s) : u x = f x := hs.extend_of_ind huc x
  refine ⟨u, hu, hf.mono (fun x hx => heq ⟨x, hx⟩), ?_⟩
  intro x y
  apply hs.induction (P := fun x => dist (u x) (u y) ≤ (K : ℝ) * dist x y ^ α) _ _ x
  · intro a ha
    apply hs.induction (P := fun y => dist (u a) (u y) ≤ (K : ℝ) * dist a y ^ α) _ _ y
    · intro b hb
      simpa only [heq ⟨a, ha⟩, heq ⟨b, hb⟩] using hbound ⟨a, ha⟩ ⟨b, hb⟩
    · exact isClosed_le (continuous_const.dist hu)
        (continuous_const.mul ((continuous_const.dist continuous_id).rpow_const (fun _ => Or.inr hα.le)))
  · exact isClosed_le (hu.dist continuous_const)
      (continuous_const.mul ((continuous_id.dist continuous_const).rpow_const (fun _ => Or.inr hα.le)))
