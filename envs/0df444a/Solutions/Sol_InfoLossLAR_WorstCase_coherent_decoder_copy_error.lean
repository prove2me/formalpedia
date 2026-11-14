-- Prove2me | solution 1 for InfoLossLAR.WorstCase.coherent_decoder_copy_error
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-13T22:47:14.632173+00:00
-- url     : https://prove2.me/submissions/a8646962-8d7c-40b7-8b29-317f76cdd217

import Mathlib

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentDecoder

/-- Copying a classical output into a fresh basis register. The first coordinate retains
all of the decoder's workspace, including deferred measurement registers. -/
noncomputable def copied {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ψ : α → ℂ) (readout : α → β) : EuclideanSpace ℂ (α × β) :=
  open Classical in
  WithLp.toLp 2 (fun p => if p.2 = readout p.1 then ψ p.1 else 0)

private theorem row_error {β : Type*} [Fintype β] [DecidableEq β] (z : ℂ) (a b : β) :
    (∑ y : β, ‖(if y = a then z else 0) - (if y = b then z else 0)‖ ^ 2) =
      if a = b then 0 else 2 * ‖z‖ ^ 2 := by
  classical
  by_cases hab : a = b
  · simp [hab]
  · have hrow (y : β) :
        ‖(if y = a then z else 0) - (if y = b then z else 0)‖ ^ 2 =
          (if y = a then ‖z‖ ^ 2 else 0) + (if y = b then ‖z‖ ^ 2 else 0) := by
      by_cases hya : y = a <;> by_cases hyb : y = b <;> simp_all
    simp_rw [hrow]
    simp [Finset.sum_add_distrib, hab, two_mul]

/-- Exact error of copying a computed answer rather than the unique desired answer.
The answer may depend on a preserved query register, so the assertion applies to a
superposition of queries as well as to a single classical input. -/
theorem copied_error_sq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ψ : α → ℂ) (readout desired : α → β) :
    ‖copied ψ readout - copied ψ desired‖ ^ 2 =
      2 * ∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, copied, PiLp.sub_apply]
  simp_rw [row_error]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Uncomputation preserves the exact error. This is a semantic statement about a
linear isometry, and does not assert a circuit implementation or its time bound. -/
theorem uncompute_error_sq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (uncompute : EuclideanSpace ℂ (α × β) →ₗᵢ[ℂ] E)
    (ψ : α → ℂ) (readout desired : α → β) :
    ‖uncompute (copied ψ readout) - uncompute (copied ψ desired)‖ ^ 2 =
      2 * ∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2 := by
  rw [← map_sub, uncompute.norm_map]
  exact copied_error_sq ψ readout desired

/-- The usual twice-square-root estimate follows from the sharper exact identity. -/
theorem uncompute_error_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (uncompute : EuclideanSpace ℂ (α × β) →ₗᵢ[ℂ] E)
    (ψ : α → ℂ) (readout desired : α → β) (ε : ℝ)
    (hfailure : (∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2) ≤ ε) :
    ‖uncompute (copied ψ readout) - uncompute (copied ψ desired)‖ ≤
      2 * Real.sqrt ε := by
  classical
  have hn : 0 ≤ ∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2 :=
    Finset.sum_nonneg fun x _ => by split_ifs <;> positivity
  have he : 0 ≤ ε := hn.trans hfailure
  have hs := Real.sq_sqrt he
  have hsq := uncompute_error_sq uncompute ψ readout desired
  have hnorm := norm_nonneg (uncompute (copied ψ readout) - uncompute (copied ψ desired))
  have hroot := Real.sqrt_nonneg ε
  nlinarith


/-- With a query register retained, the coherent error is the query-amplitude-weighted
failure probability. This keeps the whole workspace instead of treating the output bit
as if it were independent of the decoder's garbage. -/
theorem query_error_sq {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
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
theorem pool_query_mean_square_le {Ω ι α β : Type*} [Fintype Ω] [Fintype ι]
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
    simp only [mul_assoc, mul_left_comm]
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ x : ι, ‖amplitude x‖ ^ 2 * ε :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfailure x) (sq_nonneg _)
    _ = ε := by rw [← Finset.sum_mul, hamplitude, one_mul]

/-- A mean-square estimate controls mean coherent error, without selecting a single
sample pool on which all queries are simultaneously correct. -/
theorem mean_error_le {Ω : Type*} [Fintype Ω]
    (pool error : Ω → ℝ) (ε : ℝ)
    (hpool : ∀ ω, 0 ≤ pool ω) (hmass : ∑ ω, pool ω = 1)
    (hsq : (∑ ω, pool ω * (error ω) ^ 2) ≤ 2 * ε) :
    (∑ ω, pool ω * error ω) ≤ 2 * Real.sqrt ε := by
  have hnonneg : 0 ≤ ∑ ω, pool ω * (error ω) ^ 2 :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (hpool ω) (sq_nonneg _)
  have he : 0 ≤ ε := by linarith
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun ω _ => hpool ω)
    (fun ω _ => mul_nonneg (hpool ω) (sq_nonneg (error ω)))
    (fun ω _ => (show (pool ω * error ω) ^ 2 ≤
      pool ω * (pool ω * (error ω) ^ 2) by nlinarith [sq_nonneg (pool ω * error ω)]))
  rw [hmass, one_mul] at hcs
  have hs := Real.sq_sqrt he
  have hroot := Real.sqrt_nonneg ε
  nlinarith

end InfoLossLAR.WorstCase.CoherentDecoder


theorem solution
    {α β E : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (U : EuclideanSpace ℂ (α × β) →ₗᵢ[ℂ] E)
    (ψ : α → ℂ) (readout desired : α → β) (ε : ℝ)
    (hfailure : (∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2) ≤ ε) :
    let actual : EuclideanSpace ℂ (α × β) :=
      WithLp.toLp 2 (fun p => if p.2 = readout p.1 then ψ p.1 else 0)
    let ideal : EuclideanSpace ℂ (α × β) :=
      WithLp.toLp 2 (fun p => if p.2 = desired p.1 then ψ p.1 else 0)
    ‖U actual - U ideal‖ ^ 2 =
      (2 * ∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2) ∧
    ‖U actual - U ideal‖ ≤ 2 * Real.sqrt ε := by
  constructor
  · exact InfoLossLAR.WorstCase.CoherentDecoder.uncompute_error_sq U ψ readout desired
  · exact InfoLossLAR.WorstCase.CoherentDecoder.uncompute_error_le U ψ readout desired ε hfailure
