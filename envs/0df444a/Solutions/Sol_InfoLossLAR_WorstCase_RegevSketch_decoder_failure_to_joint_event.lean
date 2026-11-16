-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.decoder_failure_to_joint_event
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:22:10.280044+00:00
-- url     : https://prove2.me/submissions/81268da2-d186-4e43-babb-e3c9df58a70d

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_source_replacement_joint_hybrid
import Theorems.Thm_InfoLossLAR_WorstCase_coherent_decoder_copy_error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open RegevJointHybrid
noncomputable section

private def copied {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ψ : α → ℂ) (readout : α → β) : EuclideanSpace ℂ (α × β) :=
  open Classical in
  WithLp.toLp 2 (fun p => if p.2 = readout p.1 then ψ p.1 else 0)
private theorem copied_error_sq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ψ : α → ℂ) (readout desired : α → β) :
    ‖copied ψ readout - copied ψ desired‖ ^ 2 =
      2 * ∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2 := by
  let error := ∑ x : α, if readout x = desired x then (0 : ℝ) else ‖ψ x‖ ^ 2
  have h := (InfoLossLAR.WorstCase.coherent_decoder_copy_error
    (LinearIsometry.id : EuclideanSpace ℂ (α × β) →ₗᵢ[ℂ] EuclideanSpace ℂ (α × β))
    ψ readout desired error le_rfl).1
  simpa [copied] using h

/-- With a query register retained, the coherent error is the query-amplitude-weighted
failure probability. This keeps the whole workspace instead of treating the output bit
as if it were independent of the decoder's garbage. -/
private theorem query_error_sq {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq β] (amplitude : ι → ℂ) (ψ : ι → α → ℂ)
    (readout : ι → α → β) (answer : ι → β) :
    ‖copied (fun p : ι × α => amplitude p.1 * ψ p.1 p.2)
        (fun p => readout p.1 p.2) -
      copied (fun p : ι × α => amplitude p.1 * ψ p.1 p.2)
        (fun p => answer p.1)‖ ^ 2 =
      2 * ∑ x : ι, ‖amplitude x‖ ^ 2 *
        ∑ a : α, if readout x a = answer x then 0 else ‖ψ x a‖ ^ 2 := by
  rw [copied_error_sq, Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · simp
  · simp only [norm_mul, mul_pow]

/-- Averaging the stored sample pool is compatible with a coherent query state independent
of that pool. Only average failure for each query is required; no fixed pool needs to be
good for every query. -/
private theorem pool_query_mean_square_le {Ω ι α β : Type*} [Fintype Ω] [Fintype ι]
    [Fintype α] [Fintype β] [DecidableEq β]
    (pool : Ω → ℝ) (amplitude : ι → ℂ)
    (ψ : Ω → ι → α → ℂ) (readout : Ω → ι → α → β) (answer : ι → β)
    (ε : ℝ) (hamplitude : ∑ x : ι, ‖amplitude x‖ ^ 2 = 1)
    (hfailure : ∀ x : ι, (∑ ω : Ω, pool ω *
      ∑ a : α, if readout ω x a = answer x then 0 else ‖ψ ω x a‖ ^ 2) ≤ ε) :
    (∑ ω : Ω, pool ω *
      ‖copied (fun p : ι × α => amplitude p.1 * ψ ω p.1 p.2)
          (fun p => readout ω p.1 p.2) -
        copied (fun p : ι × α => amplitude p.1 * ψ ω p.1 p.2)
          (fun p => answer p.1)‖ ^ 2) ≤ 2 * ε := by
  simp_rw [query_error_sq]
  have heq : (∑ ω : Ω, pool ω *
      (2 * ∑ x : ι, ‖amplitude x‖ ^ 2 *
        ∑ a : α, if readout ω x a = answer x then 0 else ‖ψ ω x a‖ ^ 2)) =
      2 * ∑ x : ι, ‖amplitude x‖ ^ 2 *
        ∑ ω : Ω, pool ω *
          ∑ a : α, if readout ω x a = answer x then 0 else ‖ψ ω x a‖ ^ 2 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro ω _
    simp only [mul_left_comm]
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ x : ι, ‖amplitude x‖ ^ 2 * ε :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfailure x) (sq_nonneg _)
    _ = ε := by rw [← Finset.sum_mul, hamplitude, one_mul]


theorem solution
    {Ω ι W β α : Type*} [Fintype Ω] [Fintype ι] [Fintype W]
    [Fintype β] [Fintype α] [DecidableEq β]
    (actualPool referencePool : Ω → ℝ)
    (hp : ∀ sample, 0 ≤ actualPool sample) (hq : ∀ sample, 0 ≤ referencePool sample)
    (hpmass : ∑ sample, actualPool sample = 1)
    (hqmass : ∑ sample, referencePool sample = 1)
    (sourceError : ℝ)
    (hsource : (∑ sample, |actualPool sample-referencePool sample|) ≤ 2*sourceError)
    (actual : Ω → ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (ideal : ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (count : ℕ) (state : EuclideanSpace ℂ α) (hstate : ‖state‖ = 1)
    (event : α → Prop) (failure : ℕ → ℝ)
    (amplitude : ℕ → ι → ℂ) (work : Ω → ℕ → ι → W → ℂ)
    (readout : Ω → ℕ → ι → W → β) (answer : ℕ → ι → β)
    (uncompute : Ω → ℕ → EuclideanSpace ℂ ((ι × W) × β) →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (hamplitude : ∀ index < count, ∑ query, ‖amplitude index query‖^2 = 1)
    (hfailure : ∀ index < count, ∀ query,
      (∑ pool, referencePool pool *
        ∑ workState, if readout pool index query workState = answer index query
          then 0 else ‖work pool index query workState‖^2) ≤ failure index)
    (hactual : ∀ pool index, index < count →
      actual pool index (evolve ideal index state) =
        uncompute pool index (WithLp.toLp 2 (fun p : (ι × W) × β =>
          if p.2 = readout pool index p.1.1 p.1.2 then
            amplitude index p.1.1 * work pool index p.1.1 p.1.2 else 0)))
    (hideal : ∀ pool index, index < count →
      ideal index (evolve ideal index state) =
        uncompute pool index (WithLp.toLp 2 (fun p : (ι × W) × β =>
          if p.2 = answer index p.1.1 then
            amplitude index p.1.1 * work pool index p.1.1 p.1.2 else 0))) :
    |(∑ sample, actualPool sample * bornEvent event (evolve (actual sample) count state)) -
      bornEvent event (evolve ideal count state)| ≤
      sourceError + ∑ index ∈ Finset.range count, 4*Real.sqrt (failure index) := by
  apply InfoLossLAR.WorstCase.RegevSketch.source_replacement_joint_hybrid actualPool referencePool hp hq hpmass hqmass sourceError hsource
    actual ideal count state hstate event failure
  intro index hi
  have hstep : (∑ pool, referencePool pool *
      ‖copied (fun p : ι × W => amplitude index p.1 * work pool index p.1 p.2)
          (fun p => readout pool index p.1 p.2) -
        copied (fun p : ι × W => amplitude index p.1 * work pool index p.1 p.2)
          (fun p => answer index p.1)‖^2) ≤ 2*failure index :=
    pool_query_mean_square_le referencePool (amplitude index)
      (fun pool => work pool index) (fun pool => readout pool index) (answer index)
      (failure index) (hamplitude index hi) (hfailure index hi)
  calc
    _ = ∑ pool, referencePool pool *
      ‖copied (fun p : ι × W => amplitude index p.1 * work pool index p.1 p.2)
          (fun p => readout pool index p.1 p.2) -
        copied (fun p : ι × W => amplitude index p.1 * work pool index p.1 p.2)
          (fun p => answer index p.1)‖^2 := by
      apply Finset.sum_congr rfl
      intro pool _
      rw [hactual pool index hi, hideal pool index hi, ← map_sub, (uncompute pool index).norm_map]
      rfl
    _ ≤ _ := hstep

end
