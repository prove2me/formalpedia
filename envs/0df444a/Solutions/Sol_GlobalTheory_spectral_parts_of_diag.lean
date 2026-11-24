-- Prove2me | solution 1 for GlobalTheory.spectral_parts_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:47.731935+00:00
-- url     : https://prove2.me/submissions/1fd2c98d-8953-400d-bea0-f3d5aa4b9ce6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianSpectralPartsAnticommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (Y J U : Matrix n n ℂ)
    (μ : n → ℝ) (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    (hY : Y = U * diagonal (fun j => (μ j : ℂ)) * Uᴴ) (hJ : J * Y = -(Y * J)) :
    ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧
      (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧
        N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧
        J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by
  classical
  set φ : (ℝ → ℝ) → Matrix n n ℂ := fun f => U * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * Uᴴ
    with hφ
  have hcongr : ∀ f g : ℝ → ℝ, (∀ x, f x = g x) → φ f = φ g := by
    intro f g h
    rw [show f = g from funext h]
  have hmul : ∀ f g : ℝ → ℝ, φ f * φ g = φ (fun x => f x * g x) := by
    intro f g
    simp only [hφ]
    calc U * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * Uᴴ *
          (U * diagonal (fun j => ((g (μ j) : ℝ) : ℂ)) * Uᴴ)
        = U * (diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * (Uᴴ * U) *
          diagonal (fun j => ((g (μ j) : ℝ) : ℂ))) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [h1, Matrix.mul_one, diagonal_mul_diagonal]
        simp only [Complex.ofReal_mul]
  have hsmul : ∀ (c : ℝ) (f : ℝ → ℝ), (c : ℂ) • φ f = φ (fun x => c * f x) := by
    intro c f
    simp only [hφ]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    funext j
    simp
  have hherm : ∀ f : ℝ → ℝ, (φ f).IsHermitian := by
    intro f
    simp only [hφ]
    apply isHermitian_mul_mul_conjTranspose
    rw [isHermitian_diagonal_iff]
    intro j
    exact Complex.conj_ofReal _
  have hid : Y = φ (fun x => x) := hY
  set K := Uᴴ * J * U with hK
  have hJK : J = U * K * Uᴴ := by
    rw [hK]
    calc J = (U * Uᴴ) * J * (U * Uᴴ) := by rw [h2]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hKD : K * diagonal (fun j => (μ j : ℂ)) = -(diagonal (fun j => (μ j : ℂ)) * K) := by
    have e := congrArg (fun M => Uᴴ * M * U) hJ
    simp only [hY] at e
    have a1 : Uᴴ * (J * (U * diagonal (fun j => (μ j : ℂ)) * Uᴴ)) * U
        = K * diagonal (fun j => (μ j : ℂ)) * (Uᴴ * U) := by
      simp only [hK, Matrix.mul_assoc]
    have a2 : Uᴴ * (-(U * diagonal (fun j => (μ j : ℂ)) * Uᴴ * J)) * U
        = -((Uᴴ * U) * diagonal (fun j => (μ j : ℂ)) * K) := by
      simp only [hK, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
    rw [a1, a2, h1, Matrix.mul_one, Matrix.one_mul] at e
    exact e
  have hkey : ∀ f : ℝ → ℝ, J * φ f = φ (fun x => f (-x)) * J := by
    intro f
    have hK2 : K * diagonal (fun j => ((f (μ j) : ℝ) : ℂ))
        = diagonal (fun j => ((f (-μ j) : ℝ) : ℂ)) * K := by
      ext i j
      have e := congrFun (congrFun hKD i) j
      simp only [mul_diagonal, diagonal_mul, Matrix.neg_apply] at e ⊢
      by_cases h0 : K i j = 0
      · simp [h0]
      · have : (μ j : ℂ) = -(μ i : ℂ) := by
          apply mul_left_cancel₀ h0
          rw [e]; ring
        have h3 : μ j = -μ i := by exact_mod_cast this
        rw [h3, mul_comm]
    simp only [hφ]
    rw [hJK]
    calc U * K * Uᴴ * (U * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * Uᴴ)
        = U * (K * (Uᴴ * U) * diagonal (fun j => ((f (μ j) : ℝ) : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * (diagonal (fun j => ((f (-μ j) : ℝ) : ℂ)) * (Uᴴ * U) * K) * Uᴴ := by
          rw [h1, Matrix.mul_one, Matrix.mul_one, hK2]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hs1 : ∀ x : ℝ, x * Real.sign x = |x| := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · simp [h]
    · rw [Real.sign_of_pos h, abs_of_pos h]; ring
  have hs2 : ∀ x : ℝ, |x| * Real.sign x = x := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · simp [h]
    · rw [Real.sign_of_pos h, abs_of_pos h]; ring
  refine ⟨Finset.univ.image (fun j => |μ j|),
    fun ν => φ (fun x => if |x| = ν then Real.sign x else 0),
    fun ν => φ (fun x => if |x| = ν then 1 else 0), ?_, ?_, ?_⟩
  · simp only [hsmul]
    simp only [hφ]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hY]
    congr 2
    ext i j
    rw [Matrix.sum_apply]
    by_cases hij : i = j
    · subst hij
      simp only [diagonal_apply_eq]
      rw [Finset.sum_eq_single |μ i|]
      · simp only [if_true, hs2]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_image_of_mem (fun j => |μ j|) (Finset.mem_univ i)) h
    · simp [diagonal_apply_ne _ hij]
  · intro ν
    clear hY hK hKD hJK hφ
    clear_value φ
    beta_reduce
    refine ⟨hherm _, hherm _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [hs1, h, mul_one]
      · simp
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [mul_comm, hs1, h, mul_one]
      · simp
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [← h, hs2, mul_one]
      · simp
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [← h, hs2, one_mul]
      · simp
    · have : ∀ f : ℝ → ℝ, -φ f = φ (fun x => -f x) := by
        intro f
        have := hsmul (-1) f
        simpa using this
      rw [hkey, ← Matrix.neg_mul, this]
      congr 1
      apply hcongr; intro x
      rw [abs_neg]
      split_ifs with h
      · exact Real.sign_neg
      · simp
    · rw [hkey]
      congr 1
      apply hcongr; intro x
      rw [abs_neg]
  · intro ν ν'
    clear hY hK hKD hJK hφ hkey hs1 hs2 hherm hsmul hid
    clear_value φ
    beta_reduce
    exact (hmul _ _).trans ((hcongr _ _ fun x => mul_comm _ _).trans (hmul _ _).symm)
end GlobalTheory
