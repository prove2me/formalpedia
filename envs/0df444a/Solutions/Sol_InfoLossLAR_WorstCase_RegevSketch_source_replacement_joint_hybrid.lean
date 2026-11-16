-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.source_replacement_joint_hybrid
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:26:47.854479+00:00
-- url     : https://prove2.me/submissions/3816f05d-a85b-42a6-8c37-16516420121e

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_joint_coherent_pool_bound
set_option autoImplicit false
open scoped BigOperators
open RegevJointHybrid
noncomputable section

private theorem bounded_test_tv {Ω : Type*} [Fintype Ω]
    (p q test : Ω → ℝ) (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1)
    (htest : ∀ x, 0 ≤ test x ∧ test x ≤ 1)
    (δ : ℝ) (htv : (∑ x, |p x - q x|) ≤ 2*δ) :
    |(∑ x, p x * test x) - (∑ x, q x * test x)| ≤ δ := by
  have hzero : (∑ x, (p x - q x)) = 0 := by simp [Finset.sum_sub_distrib, hp, hq]
  have hcenter : (∑ x, (p x - q x) * test x) =
      ∑ x, (p x - q x) * (test x - 1/2) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ←Finset.sum_mul, hzero, zero_mul, sub_zero]
  have hterm (x : Ω) : |(p x-q x)*(test x-1/2)| ≤ |p x-q x|/2 := by
    rw [abs_mul]
    have h : |test x-1/2| ≤ (1/2 : ℝ) := by
      apply abs_le.mpr
      obtain ⟨h1,h2⟩ := htest x
      constructor <;> linarith
    nlinarith [mul_nonneg (abs_nonneg (p x-q x)) (sub_nonneg.mpr h)]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hterm x)
  have habs := Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset Ω))
    (f := fun x => (p x-q x)*(test x-1/2))
  rw [←Finset.sum_div] at hsum
  have htv' : (∑ x, |p x-q x|) / 2 ≤ δ := by linarith
  calc
    _ = |∑ x, (p x - q x) * test x| := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ = |∑ x, (p x - q x) * (test x - 1/2)| := by rw [hcenter]
    _ ≤ ∑ x, |(p x - q x) * (test x - 1/2)| := habs
    _ ≤ (∑ x, |p x-q x|)/2 := hsum
    _ ≤ δ := htv'

private theorem norm_evolve {α : Type*} [Fintype α]
    (step : ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (count : ℕ) (state : EuclideanSpace ℂ α) :
    ‖evolve step count state‖ = ‖state‖ := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [evolve,LinearIsometry.norm_map] using ih

private theorem born_unit_bounds {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) (hstate : ‖state‖=1) :
    0 ≤ bornEvent event state ∧ bornEvent event state ≤ 1 := by
  classical
  have hnonneg : 0 ≤ bornEvent event state := by
    unfold bornEvent
    exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  have hbound : bornEvent event state ≤ ∑ x, ‖state x‖^2 := by
    unfold bornEvent
    apply Finset.sum_le_sum
    intro x _
    split_ifs <;> simp_all
  have heq : (∑ x, ‖state x‖^2) = (1 : ℝ) := by
    rw [←EuclideanSpace.norm_sq_eq,hstate]
    norm_num
  exact ⟨hnonneg, hbound.trans_eq heq⟩

theorem solution {Ω α : Type*} [Fintype Ω] [Fintype α]
    (actualPool referencePool : Ω → ℝ)
    (_hp : ∀ sample, 0 ≤ actualPool sample) (hq : ∀ sample, 0 ≤ referencePool sample)
    (hpmass : ∑ sample, actualPool sample = 1)
    (hqmass : ∑ sample, referencePool sample = 1)
    (sourceError : ℝ)
    (hsource : (∑ sample, |actualPool sample-referencePool sample|) ≤ 2*sourceError)
    (actual : Ω → ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (ideal : ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (count : ℕ) (state : EuclideanSpace ℂ α) (hstate : ‖state‖ = 1)
    (event : α → Prop) (failure : ℕ → ℝ)
    (hstep : ∀ index<count,
      (∑ sample,referencePool sample*
        ‖actual sample index (evolve ideal index state)-ideal index (evolve ideal index state)‖^2) ≤
          2*failure index) :
    |(∑ sample, actualPool sample * bornEvent event (evolve (actual sample) count state)) -
      bornEvent event (evolve ideal count state)| ≤
      sourceError + ∑ index ∈ Finset.range count, 4*Real.sqrt (failure index) := by
  let outcome := fun sample => bornEvent event (evolve (actual sample) count state)
  let idealValue := bornEvent event (evolve ideal count state)
  have houtcome : ∀ sample, 0 ≤ outcome sample ∧ outcome sample ≤ 1 := by
    intro sample
    apply born_unit_bounds
    simpa only [norm_evolve] using hstate
  have hrepl := bounded_test_tv actualPool referencePool outcome hpmass hqmass houtcome sourceError hsource
  have hhybrid := InfoLossLAR.WorstCase.RegevSketch.joint_coherent_pool_bound
    referencePool hq hqmass actual ideal count state hstate event failure hstep
  have hsecond : |(∑ sample, referencePool sample * outcome sample) - idealValue| ≤
      ∑ index ∈ Finset.range count, 4*Real.sqrt (failure index) := by
    have hmass : (∑ sample, referencePool sample * idealValue) = idealValue := by
      rw [←Finset.sum_mul,hqmass,one_mul]
    rw [←hmass, ←Finset.sum_sub_distrib]
    simp_rw [←mul_sub]
    have htriangle := Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset Ω))
      (f := fun sample => referencePool sample * (outcome sample - idealValue))
    simp_rw [abs_mul,abs_of_nonneg (hq _)] at htriangle
    exact htriangle.trans hhybrid
  have htri := abs_sub_le (∑ sample, actualPool sample * outcome sample)
    (∑ sample, referencePool sample * outcome sample) idealValue
  exact htri.trans (add_le_add hrepl hsecond)

end
