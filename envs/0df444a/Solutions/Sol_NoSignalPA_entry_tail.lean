-- Prove2me | solution 1 for NoSignalPA.entry_tail
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:56:44.14209+00:00
-- url     : https://prove2.me/submissions/7f391747-59fa-4ef8-acc3-04a8b9993aa1

import Mathlib
import Definitions.Def_NoSignalPA_gammaVec
import Definitions.Def_NoSignalPA_ones
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Theorems.Thm_NoSignalPA_bernstein_chain
import Theorems.Thm_NoSignalPA_sum_mu
import Theorems.Thm_NoSignalPA_abs_mu_le

namespace NoSignalPATailAux

lemma uniformProbability_mono {α : Type} [Fintype α] (P Q : α → Prop) (h : ∀ ω, P ω → Q ω) :
    OAI.ThorpCompatibility.uniformProbability P ≤ OAI.ThorpCompatibility.uniformProbability Q := by
  classical
  unfold OAI.ThorpCompatibility.uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card fun ω hω => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω

/-- Bernstein's bound (the chain (14) collapsed), for any weights `ν` with `|β ν| ≤ 1`. -/
lemma bernstein_bound {Nr Ns : ℕ} (k : NoSignalPA.Str Ns) (ν : NoSignalPA.Str Nr → ℝ) (J β : ℝ)
    (hβ : 0 ≤ β) (hsmall : ∀ s, |β * ν s| ≤ 1) :
    OAI.ThorpCompatibility.uniformProbability (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns =>
        J ≤ ∑ s, ν s * (if h s = k then 1 else 0))
      ≤ Real.exp (-β * J + ((2 : ℝ) ^ Ns)⁻¹ * ∑ s, (β * ν s + β ^ 2 * ν s ^ 2)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := NoSignalPA.bernstein_chain k ν J β hβ
  have h4' := h4 hsmall
  have hE : 0 ≤ Real.exp (-β * J) := (Real.exp_pos _).le
  exact h1.trans (h2.trans (h3.trans (h4'.trans h5)))

lemma two_rpow_mul (x y : ℝ) : (2 : ℝ) ^ x * (2 : ℝ) ^ y = (2 : ℝ) ^ (x + y) :=
  (Real.rpow_add (by norm_num) x y).symm

lemma four_pow (n : ℕ) : (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * (n : ℝ)) := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, ← Real.rpow_natCast]
  push_cast
  ring_nf

lemma eight_pow (n : ℕ) : (8 : ℝ) ^ n = (2 : ℝ) ^ (3 * (n : ℝ)) := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← pow_mul, ← Real.rpow_natCast]
  push_cast
  ring_nf

lemma two_pow (n : ℕ) : (2 : ℝ) ^ n = (2 : ℝ) ^ (n : ℝ) := (Real.rpow_natCast 2 n).symm

end NoSignalPATailAux

open NoSignalPATailAux in
theorem solution {Nr Ns : ℕ} (hN : (Ns : ℝ) + Real.sqrt Nr ≤ Nr + 2) (k : NoSignalPA.Str Ns)
    (a₀ b₀ x₀ y₀ : NoSignalPA.Str Nr) :
    let μ : NoSignalPA.Str Nr → ℝ := fun s => NoSignalPA.gammaVec s a₀ b₀ x₀ y₀
    let M : ℕ := NoSignalPA.ones (fun i => xor (xor (a₀ i) (b₀ i)) (x₀ i && y₀ i))
    let c : ℝ := (2 : ℝ) ^ (-(Ns : ℝ) - 2 * Nr)
    let T : ℝ := (2 : ℝ) ^ ((Real.sqrt Nr - Nr - Ns) / 2) * ((4 : ℝ) ^ Nr)⁻¹ * 5 ^ M
    OAI.ThorpCompatibility.uniformProbability (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns =>
        c + T ≤ ∑ s, μ s * (if h s = k then 1 else 0))
        ≤ Real.exp (-((2 : ℝ) ^ Real.sqrt Nr) / 4) ∧
      OAI.ThorpCompatibility.uniformProbability (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns =>
        ∑ s, μ s * (if h s = k then 1 else 0) ≤ c - T)
        ≤ Real.exp (-((2 : ℝ) ^ Real.sqrt Nr) / 4) := by
  intro μ M c T
  set s := Real.sqrt (Nr : ℝ) with hs
  set p : ℝ := ((2 : ℝ) ^ Ns)⁻¹ with hp
  -- moments of `μ` (Proved milestones)
  obtain ⟨hsum1, hsum2⟩ := NoSignalPA.sum_mu a₀ b₀ x₀ y₀
  have habs : ∀ t, |μ t| ≤ 5 ^ M * ((8 : ℝ) ^ Nr)⁻¹ := fun t => NoSignalPA.abs_mu_le t a₀ b₀ x₀ y₀
  -- the parameter
  set β : ℝ := (2 : ℝ) ^ ((s + Ns + 5 * Nr) / 2 - 1) * ((5 : ℝ) ^ M)⁻¹ with hβdef
  have h5 : (0 : ℝ) < (5 : ℝ) ^ M := by positivity
  have hβ0 : 0 ≤ β := by positivity
  -- `β · 5^M 8^{-Nr} = 2^{(√Nr + Ns - Nr)/2 - 1} ≤ 1`
  have hsmall : ∀ t, |β * μ t| ≤ 1 := by
    intro t
    rw [abs_mul, abs_of_nonneg hβ0]
    calc β * |μ t| ≤ β * (5 ^ M * ((8 : ℝ) ^ Nr)⁻¹) := mul_le_mul_of_nonneg_left (habs t) hβ0
      _ = (2 : ℝ) ^ ((s + Ns - Nr) / 2 - 1) := by
          rw [hβdef, eight_pow, ← Real.rpow_neg (by norm_num)]
          rw [show (2 : ℝ) ^ ((s + Ns + 5 * Nr) / 2 - 1) * ((5 : ℝ) ^ M)⁻¹ *
              ((5 : ℝ) ^ M * (2 : ℝ) ^ (-(3 * (Nr : ℝ)))) =
              (2 : ℝ) ^ ((s + Ns + 5 * Nr) / 2 - 1) * (2 : ℝ) ^ (-(3 * (Nr : ℝ))) *
                (((5 : ℝ) ^ M)⁻¹ * (5 : ℝ) ^ M) by ring]
          rw [inv_mul_cancel₀ h5.ne', mul_one, two_rpow_mul]
          congr 1
          ring
      _ ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          linarith
  have hsmall' : ∀ t, |β * (-μ t)| ≤ 1 := by
    intro t
    rw [mul_neg, abs_neg]
    exact hsmall t
  -- the identities `βT = 2^{√Nr}/2`, `p β² D = 2^{√Nr}/4`, `p Σμ = c`
  have hβT : β * T = (2 : ℝ) ^ s / 2 := by
    simp only [hβdef, T]
    rw [four_pow, ← Real.rpow_neg (by norm_num)]
    rw [show (2 : ℝ) ^ ((s + Ns + 5 * Nr) / 2 - 1) * ((5 : ℝ) ^ M)⁻¹ *
        ((2 : ℝ) ^ ((s - Nr - Ns) / 2) * (2 : ℝ) ^ (-(2 * (Nr : ℝ))) * (5 : ℝ) ^ M) =
        (2 : ℝ) ^ ((s + Ns + 5 * Nr) / 2 - 1) * (2 : ℝ) ^ ((s - Nr - Ns) / 2) *
          (2 : ℝ) ^ (-(2 * (Nr : ℝ))) * (((5 : ℝ) ^ M)⁻¹ * (5 : ℝ) ^ M) by ring]
    rw [inv_mul_cancel₀ h5.ne', mul_one, two_rpow_mul, two_rpow_mul]
    rw [show (s + Ns + 5 * Nr) / 2 - 1 + (s - Nr - Ns) / 2 + -(2 * (Nr : ℝ)) = s + (-1) by ring,
      Real.rpow_add (by norm_num), Real.rpow_neg_one]
    ring
  have hD : p * β ^ 2 * (((2 : ℝ) ^ (5 * Nr))⁻¹ * 5 ^ (2 * M)) = (2 : ℝ) ^ s / 4 := by
    have e1 : β ^ 2 = (2 : ℝ) ^ (s + Ns + 5 * Nr - 2) * (((5 : ℝ) ^ M) ^ 2)⁻¹ := by
      rw [hβdef, mul_pow, inv_pow, ← Real.rpow_natCast ((2 : ℝ) ^ _) 2,
        ← Real.rpow_mul (by norm_num)]
      congr 2
      push_cast
      ring
    have e2 : p = (2 : ℝ) ^ (-(Ns : ℝ)) := by
      rw [hp, two_pow Ns, Real.rpow_neg (by norm_num)]
    have e3 : ((2 : ℝ) ^ (5 * Nr))⁻¹ = (2 : ℝ) ^ (-(5 * (Nr : ℝ))) := by
      rw [two_pow (5 * Nr), Real.rpow_neg (by norm_num)]
      push_cast
      ring_nf
    have e4 : (5 : ℝ) ^ (2 * M) = ((5 : ℝ) ^ M) ^ 2 := by rw [mul_comm, pow_mul]
    have h52 : ((5 : ℝ) ^ M) ^ 2 ≠ 0 := by positivity
    rw [e1, e2, e3, e4]
    rw [show (2 : ℝ) ^ (-(Ns : ℝ)) * ((2 : ℝ) ^ (s + Ns + 5 * Nr - 2) * (((5 : ℝ) ^ M) ^ 2)⁻¹) *
        ((2 : ℝ) ^ (-(5 * (Nr : ℝ))) * ((5 : ℝ) ^ M) ^ 2) =
        (2 : ℝ) ^ (-(Ns : ℝ)) * (2 : ℝ) ^ (s + Ns + 5 * Nr - 2) * (2 : ℝ) ^ (-(5 * (Nr : ℝ))) *
          ((((5 : ℝ) ^ M) ^ 2)⁻¹ * ((5 : ℝ) ^ M) ^ 2) by ring]
    rw [inv_mul_cancel₀ h52, mul_one, two_rpow_mul, two_rpow_mul]
    rw [show -(Ns : ℝ) + (s + Ns + 5 * Nr - 2) + -(5 * (Nr : ℝ)) = s + (-2) by ring,
      Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num)]
    norm_num
    ring
  have hpc : p * ∑ t, μ t = c := by
    rw [hsum1, hp, four_pow, two_pow Ns, ← Real.rpow_neg (by norm_num),
      ← Real.rpow_neg (by norm_num), two_rpow_mul]
    congr 1
  have hvar : p * β ^ 2 * ∑ t, μ t ^ 2 ≤ (2 : ℝ) ^ s / 4 := by
    rw [← hD]
    exact mul_le_mul_of_nonneg_left hsum2 (by positivity)
  -- the linear and quadratic parts of the exponent
  have hlin : ∀ ε : ℝ, p * ∑ t, β * (ε * μ t) = β * ε * c := by
    intro ε
    rw [← hpc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have hquad : ∀ ε : ℝ, ε ^ 2 = 1 →
      p * ∑ t, β ^ 2 * (ε * μ t) ^ 2 = p * β ^ 2 * ∑ t, μ t ^ 2 := by
    intro ε hε
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h2 : (ε * μ t) ^ 2 = μ t ^ 2 := by rw [mul_pow ε (μ t) 2, hε, one_mul]
    rw [h2]
    ring
  refine ⟨?_, ?_⟩
  · -- upper tail: `J = c + T`, weights `μ`
    refine (bernstein_bound k μ (c + T) β hβ0 hsmall).trans (Real.exp_le_exp.mpr ?_)
    have hl := hlin 1
    have hq := hquad 1 (by norm_num)
    simp only [one_mul] at hl hq
    rw [← hp, Finset.sum_add_distrib, mul_add p, hl, hq]
    nlinarith [hβT, hvar]
  · -- lower tail: `J = T - c`, weights `-μ`
    have hev : OAI.ThorpCompatibility.uniformProbability
        (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns =>
          ∑ t, μ t * (if h t = k then 1 else 0) ≤ c - T) ≤
        OAI.ThorpCompatibility.uniformProbability
        (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns =>
          T - c ≤ ∑ t, (fun t => -μ t) t * (if h t = k then 1 else 0)) := by
      refine uniformProbability_mono _ _ fun h hX => ?_
      have : ∑ t, (fun t => -μ t) t * (if h t = k then (1 : ℝ) else 0) =
          -∑ t, μ t * (if h t = k then 1 else 0) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
      rw [this]
      linarith
    refine hev.trans ((bernstein_bound k (fun t => -μ t) (T - c) β hβ0 hsmall').trans
      (Real.exp_le_exp.mpr ?_))
    have hl := hlin (-1)
    have hq := hquad (-1) (by norm_num)
    simp only [neg_one_mul] at hl hq
    rw [← hp, Finset.sum_add_distrib, mul_add p, hl, hq]
    nlinarith [hβT, hvar]
