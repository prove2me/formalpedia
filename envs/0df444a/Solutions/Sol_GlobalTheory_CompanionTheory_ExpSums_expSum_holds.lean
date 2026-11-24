-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExpSums.expSum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:47:07.353126+00:00
-- url     : https://prove2.me/submissions/370ec0fd-1025-482c-92b9-6152f7e038e2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FibreFactorHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VandermondeSeparation
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Theorems.Thm_GlobalTheory_CompanionTheory_ExpSums_tendsto_one_add_pow_mul_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_ExpSums_vandermonde_separation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExpSums
namespace GlobalTheory.CompanionTheory.ExpSums
theorem _root_.solution : PositivityTheory.Rg.BcB.F.ExpSum := by
  intro ι _ c lam ρ C N hρ hbound μ hμ
  obtain ⟨d, hd⟩ : ∃ d : ℂ → ℂ, ∀ ν, d ν = ∑ i with lam i = ν, c i := ⟨_, fun _ => rfl⟩
  rw [← hd]
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, S = Finset.univ.image lam := ⟨_, rfl⟩
  by_cases hμS : μ ∉ S
  · rw [hd]
    refine Finset.sum_eq_zero fun i hi => absurd ?_ hμS
    rw [hS, ← (Finset.mem_filter.mp hi).2]
    exact Finset.mem_image_of_mem lam (Finset.mem_univ i)
  push_neg at hμS
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι), lam i ∈ S := fun i _ => by
    rw [hS]; exact Finset.mem_image_of_mem lam (Finset.mem_univ i)
  have hsum : ∀ k : ℕ, ∑ i, c i * lam i ^ k = ∑ ν ∈ S, d ν * ν ^ k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hd, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  obtain ⟨e, -⟩ : ∃ e : Fin S.card ≃ S, e = S.equivFin.symm := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : Fin S.card → ℂ, ∀ k, α k = (e k : ℂ) := ⟨_, fun _ => rfl⟩
  have hinj : Function.Injective α := by
    intro a b hab
    rw [hα, hα] at hab
    exact e.injective (Subtype.val_injective hab)
  have hpow : ∀ n : ℕ, ∑ k, d (α k) * α k ^ n = ∑ i, c i * lam i ^ n := by
    intro n
    rw [hsum n]
    simp only [hα]
    exact (Equiv.sum_comp e (fun x : S => d x * (x : ℂ) ^ n)).trans
      (Finset.sum_coe_sort S (fun ν => d ν * ν ^ n))
  obtain ⟨C', hC'⟩ := GlobalTheory.CompanionTheory.ExpSums.vandermonde_separation S.card α hinj
  obtain ⟨C1, hC1, hC'1⟩ : ∃ C1 : ℝ, 0 ≤ C1 ∧ C' ≤ C1 := ⟨max C' 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨C2, hC2, hCC2⟩ : ∃ C2 : ℝ, 0 ≤ C2 ∧ C ≤ C2 := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ s : Fin S.card, (1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ) := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hbound
  have hK0' : ∀ k : ℕ, K0 ≤ k → ‖∑ i, c i * lam i ^ k‖ ≤ C2 * (1 + (k : ℝ)) ^ N * ρ ^ k := by
    intro k hk
    refine (hK0 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC2 (pow_nonneg (by positivity) N)) (pow_nonneg hρ k)
  obtain ⟨j, hj⟩ : ∃ j : Fin S.card, α j = μ := ⟨e.symm ⟨μ, hμS⟩, by rw [hα, Equiv.apply_symm_apply]⟩
  have key : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ * ‖μ‖ ^ m ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) := by
    intro m hm
    have h1 := hC' (fun k => d (α k) * α k ^ m) j
    have hinner : ∀ s : Fin S.card,
        ∑ k, d (α k) * α k ^ m * α k ^ (s : ℕ) = ∑ i, c i * lam i ^ (m + (s : ℕ)) := by
      intro s
      rw [← hpow (m + (s : ℕ))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add]
      ring
    simp only [hinner, hj, norm_mul, norm_pow] at h1
    have hT : 0 ≤ ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsb : ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ ≤
        C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have hk := hK0' (m + (s : ℕ)) (le_trans hm (Nat.le_add_right m _))
      rw [Nat.cast_add] at hk
      have hbase : 1 + ((m : ℝ) + ((s : ℕ) : ℝ)) ≤ (1 + (m : ℝ)) * (1 + ((s : ℕ) : ℝ)) := by
        have hms : (0 : ℝ) ≤ (m : ℝ) * ((s : ℕ) : ℝ) := by positivity
        nlinarith
      have hle : (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N ≤ (1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hbase N
      calc ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖
          ≤ C2 * (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N * ρ ^ (m + (s : ℕ)) := hk
        _ ≤ C2 * ((1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N) * ρ ^ (m + (s : ℕ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hC2) (pow_nonneg hρ _)
        _ = C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * ((1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ)) := by
          rw [pow_add]
          ring
    calc ‖d μ‖ * ‖μ‖ ^ m ≤ C' * ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ := h1
      _ ≤ C1 * ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ :=
        mul_le_mul_of_nonneg_right hC'1 hT
      _ ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) := mul_le_mul_of_nonneg_left hsb hC1
  have hμpos : 0 < ‖μ‖ := lt_of_le_of_lt hρ hμ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ρ / ‖μ‖ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hρ (norm_nonneg _)
  have ht1 : t < 1 := by rw [ht, div_lt_one hμpos]; exact hμ
  have hlim := (tendsto_one_add_pow_mul_pow ht0 ht1 N).const_mul (C1 * (C2 * B))
  rw [mul_zero] at hlim
  have hle : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ ≤ C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * t ^ m) := by
    intro m hm
    have h := (le_div_iff₀ (pow_pos hμpos m)).mpr (key m hm)
    rw [ht, div_pow]
    calc ‖d μ‖ ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) / ‖μ‖ ^ m := h
      _ = C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * (ρ ^ m / ‖μ‖ ^ m)) := by ring
  have h0 : ‖d μ‖ ≤ 0 := ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨K0, hle⟩)
  exact norm_le_zero_iff.mp h0
end GlobalTheory.CompanionTheory.ExpSums
