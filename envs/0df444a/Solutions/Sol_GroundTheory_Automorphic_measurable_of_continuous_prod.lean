-- Prove2me | solution 1 for GroundTheory.Automorphic.measurable_of_continuous_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:02.698361+00:00
-- url     : https://prove2.me/submissions/72f28d22-2058-486d-8c11-185b4461b267

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_mem_index
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_measurable_index

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology Uniformity UniformSpace Function
open MeasurablePartition
variable {X Y : Type*} [UniformSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [UniformSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]
namespace GroundTheory.Automorphic
theorem _root_.solution {β : Type*} [PseudoMetricSpace β] [MeasurableSpace β]
    [BorelSpace β] {k : X × Y → β} (hk : Continuous k) : Measurable k := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · intro s _
    rw [Set.eq_empty_of_isEmpty (k ⁻¹' s)]
    exact MeasurableSet.empty
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y₀⟩⟩
  · intro s _
    rw [Set.eq_empty_of_isEmpty (k ⁻¹' s)]
    exact MeasurableSet.empty
  have huc : UniformContinuous k := CompactSpace.uniformContinuous_of_continuous hk

  have hent : ∀ m : ℕ, ∃ u ∈ 𝓤 X, ∃ v ∈ 𝓤 Y, ∀ x x' y y', (x, x') ∈ u → (y, y') ∈ v →
      dist (k (x, y)) (k (x', y')) < 1 / (m + 1) := by
    intro m
    have h := huc (Metric.dist_mem_uniformity (by positivity : (0 : ℝ) < 1 / (m + 1)))
    obtain ⟨u, hu, v, hv, huv⟩ := entourageProd_subset h
    exact ⟨u, hu, v, hv, fun x x' y y' hx hy => huv (show ((x, y), (x', y')) ∈
      entourageProd u v from ⟨hx, hy⟩)⟩
  choose u hu v hv huv using hent
  let p : ℕ → MeasurablePartition X := fun m => (exists_isFine (hu m)).choose
  let q : ℕ → MeasurablePartition Y := fun m => (exists_isFine (hv m)).choose
  have hp : ∀ m, (p m).IsFine (u m) := fun m => (exists_isFine (hu m)).choose_spec
  have hq : ∀ m, (q m).IsFine (v m) := fun m => (exists_isFine (hv m)).choose_spec
  classical
  let rX : MeasurablePartition X → ℕ → X := fun P i => if h : (P.E i).Nonempty then h.some else x₀
  let rY : MeasurablePartition Y → ℕ → Y := fun P i => if h : (P.E i).Nonempty then h.some else y₀
  have hrX : ∀ P i x, x ∈ P.E i → rX P i ∈ P.E i := by
    intro P i x hx
    simp only [rX, dif_pos (show (P.E i).Nonempty from ⟨x, hx⟩)]
    exact Set.Nonempty.some_mem _
  have hrY : ∀ P i y, y ∈ P.E i → rY P i ∈ P.E i := by
    intro P i y hy
    simp only [rY, dif_pos (show (P.E i).Nonempty from ⟨y, hy⟩)]
    exact Set.Nonempty.some_mem _
  let kk : ℕ → X × Y → β := fun m z =>
    k (rX (p m) ((p m).index z.1), rY (q m) ((q m).index z.2))
  have hmeas : ∀ m, Measurable (kk m) := by
    intro m
    have h1 : Measurable fun z : X × Y => ((p m).index z.1, (q m).index z.2) :=
      ((p m).measurable_index.comp measurable_fst).prodMk
        ((q m).measurable_index.comp measurable_snd)
    exact (measurable_of_countable
      (fun ij : ℕ × ℕ => k (rX (p m) ij.1, rY (q m) ij.2))).comp h1
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun z => ?_)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun m hm => ?_⟩
  have hx := (p m).mem_index z.1
  have hy := (q m).mem_index z.2
  have h1 := hp m _ _ (hrX _ _ _ hx) _ hx
  have h2 := hq m _ _ (hrY _ _ _ hy) _ hy
  refine (huv m _ _ _ _ h1 h2).trans_le ?_ |>.trans hN
  gcongr
end GroundTheory.Automorphic
