-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.joint_coherent_pool_bound
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:12:02.656194+00:00
-- url     : https://prove2.me/submissions/17977346-ef05-4cd9-9ac0-8b0d004d6885

import Definitions.Def_RegevJointHybrid
set_option autoImplicit false
open scoped BigOperators
namespace RegevJointHybrid
noncomputable section
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

theorem evolve_error_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (actual ideal : ℕ → E →ₗᵢ[ℂ] E) (count : ℕ) (state : E) :
    ‖evolve actual count state-evolve ideal count state‖ ≤
      ∑ index ∈ Finset.range count,
        ‖actual index (evolve ideal index state)-ideal index (evolve ideal index state)‖ := by
  induction count with
  | zero => simp [evolve]
  | succ count ih =>
    rw [evolve,evolve,Finset.sum_range_succ]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (actual count (evolve actual count state))
      (actual count (evolve ideal count state))
      (ideal count (evolve ideal count state))
    have hiso :
        ‖actual count (evolve actual count state)-actual count (evolve ideal count state)‖=
          ‖evolve actual count state-evolve ideal count state‖ := by
      rw [←map_sub,(actual count).norm_map]
    rw [hiso] at htri
    exact htri.trans (add_le_add ih le_rfl)

/-- A single finite sample pool may be reused for every call. Only its
average error on each ideal prefix is needed; no simultaneous good-pool
statement and no independence of the actual query state are assumed. -/
theorem pool_evolve_error_le {Ω E : Type*} [Fintype Ω]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (pool : Ω → ℝ) (hpool : ∀ sample,0 ≤ pool sample)
    (actual : Ω → ℕ → E →ₗᵢ[ℂ] E) (ideal : ℕ → E →ₗᵢ[ℂ] E)
    (count : ℕ) (state : E) (budget : ℕ → ℝ)
    (hstep : ∀ index<count,
      (∑ sample,pool sample*
        ‖actual sample index (evolve ideal index state)-ideal index (evolve ideal index state)‖) ≤
          budget index) :
    (∑ sample,pool sample*‖evolve (actual sample) count state-evolve ideal count state‖) ≤
      ∑ index ∈ Finset.range count,budget index := by
  calc
    _ ≤ ∑ sample,pool sample*(∑ index ∈ Finset.range count,
        ‖actual sample index (evolve ideal index state)-ideal index (evolve ideal index state)‖) := by
      apply Finset.sum_le_sum
      intro sample _
      exact mul_le_mul_of_nonneg_left (evolve_error_le (actual sample) ideal count state) (hpool sample)
    _ = ∑ index ∈ Finset.range count,∑ sample,pool sample*
        ‖actual sample index (evolve ideal index state)-ideal index (evolve ideal index state)‖ := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro index hi
      exact hstep index (Finset.mem_range.mp hi)

/-- Uniform mean-square error bounds combine directly with the ideal-prefix
hybrid. The pool is reused, and the total loss is linear in the number of
calls after the square-root conversion. -/
theorem pool_evolve_error_le_sqrt {Ω E : Type*} [Fintype Ω]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (pool : Ω → ℝ) (hpool : ∀ sample,0 ≤ pool sample)
    (hmass : ∑ sample,pool sample=1)
    (actual : Ω → ℕ → E →ₗᵢ[ℂ] E) (ideal : ℕ → E →ₗᵢ[ℂ] E)
    (count : ℕ) (state : E) (failure : ℕ → ℝ)
    (hstep : ∀ index<count,
      (∑ sample,pool sample*
        ‖actual sample index (evolve ideal index state)-ideal index (evolve ideal index state)‖^2) ≤
          2*failure index) :
    (∑ sample,pool sample*‖evolve (actual sample) count state-evolve ideal count state‖) ≤
      ∑ index ∈ Finset.range count,2*Real.sqrt (failure index) := by
  apply pool_evolve_error_le pool hpool actual ideal count state
  intro index hi
  exact mean_error_le pool
    (fun sample => ‖actual sample index (evolve ideal index state)-ideal index (evolve ideal index state)‖)
    (failure index) hpool hmass (hstep index hi)

def retainEvent {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) : EuclideanSpace ℂ α :=
  open Classical in WithLp.toLp 2 (fun value => if event value then state value else 0)


theorem bornEvent_eq_norm_sq {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) : bornEvent event state=‖retainEvent event state‖^2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  unfold bornEvent retainEvent
  apply Finset.sum_congr rfl
  intro value _
  split_ifs <;> simp_all

theorem retainEvent_norm_le {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) : ‖retainEvent event state‖ ≤ ‖state‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro value _
  change ‖(if event value then state value else 0 : ℂ)‖^2 ≤ ‖state value‖^2
  split_ifs <;> simp_all

theorem retainEvent_sub {α : Type*} [Fintype α] (event : α → Prop)
    (first second : EuclideanSpace ℂ α) :
    retainEvent event (first-second)=retainEvent event first-retainEvent event second := by
  classical
  ext value
  change (if event value then first value-second value else 0)=
    (if event value then first value else 0)-(if event value then second value else 0)
  split_ifs <;> simp

/-- Final classical measurement contracts coherent error. This estimate uses
the full amplitudes and does not replace correlated garbage with independent
output bits. -/
theorem bornEvent_error_le {α : Type*} [Fintype α] (event : α → Prop)
    (first second : EuclideanSpace ℂ α) :
    |bornEvent event first-bornEvent event second| ≤ ‖first-second‖*(‖first‖+‖second‖) := by
  rw [bornEvent_eq_norm_sq,bornEvent_eq_norm_sq]
  have hdiff : |‖retainEvent event first‖-‖retainEvent event second‖| ≤ ‖first-second‖ := by
    apply (abs_norm_sub_norm_le _ _).trans
    rw [←retainEvent_sub]
    exact retainEvent_norm_le event _
  have hsum := add_le_add (retainEvent_norm_le event first) (retainEvent_norm_le event second)
  calc
    _ = |‖retainEvent event first‖-‖retainEvent event second‖| *
        (‖retainEvent event first‖+‖retainEvent event second‖) := by
      rw [←abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),←abs_mul]
      congr 1
      ring
    _ ≤ _ := mul_le_mul hdiff hsum (by positivity) (norm_nonneg _)

@[simp] theorem evolve_norm {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (step : ℕ → E →ₗᵢ[ℂ] E) (count : ℕ) (state : E) :
    ‖evolve step count state‖=‖state‖ := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [evolve,LinearIsometry.norm_map] using ih


end
end RegevJointHybrid

open RegevJointHybrid
noncomputable section
theorem solution {Ω α : Type*} [Fintype Ω] [Fintype α]
    (pool : Ω → ℝ) (hpool : ∀ sample,0 ≤ pool sample)
    (hmass : ∑ sample,pool sample=1)
    (actual : Ω → ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (ideal : ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (count : ℕ) (state : EuclideanSpace ℂ α) (hstate : ‖state‖=1)
    (event : α → Prop) (failure : ℕ → ℝ)
    (hstep : ∀ index<count,
      (∑ sample,pool sample*
        ‖actual sample index (evolve ideal index state)-ideal index (evolve ideal index state)‖^2) ≤
          2*failure index) :
    (∑ sample,pool sample*|bornEvent event (evolve (actual sample) count state)-
      bornEvent event (evolve ideal count state)|) ≤
      ∑ index ∈ Finset.range count,4*Real.sqrt (failure index) := by
  calc
    _ ≤ ∑ sample,pool sample*(2*‖evolve (actual sample) count state-evolve ideal count state‖) := by
      apply Finset.sum_le_sum
      intro sample _
      apply mul_le_mul_of_nonneg_left _ (hpool sample)
      have hb := bornEvent_error_le event (evolve (actual sample) count state) (evolve ideal count state)
      rw [evolve_norm,evolve_norm,hstate] at hb
      norm_num only at hb
      simpa only [mul_comm] using hb
    _ = 2*(∑ sample,pool sample*‖evolve (actual sample) count state-evolve ideal count state‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sample _
      ring
    _ ≤ 2*(∑ index ∈ Finset.range count,2*Real.sqrt (failure index)) :=
      mul_le_mul_of_nonneg_left
        (pool_evolve_error_le_sqrt pool hpool hmass actual ideal count state failure hstep) (by norm_num)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      ring

end
