-- Prove2me | solution 1 for OAI.HadamardSix.fourth_power_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T18:17:52.957973+00:00
-- url     : https://prove2.me/submissions/eec40715-7698-4c5d-a870-260a92526e3c

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/Hadamard/Polynomials.lean:L193-L209
-- (upload_full_project.md Phase 4): solution for node OAI.HadamardSix.fourth_power_sum_zero. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_HadamardCubeFiber
import Definitions.Def_OAI_LinearAlgebra_Hadamard_Polynomials

-- ---- inline helpers from OAI.LinearAlgebra.Hadamard.Basic ----
namespace OAI

/-! Unit entries, orthogonality, characters and the cubic matrix. -/

open scoped BigOperators Matrix

namespace HadamardSix

lemma unit_mul_star {z : ℂ} (hz : ‖z‖ = 1) : z * star z = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

end HadamardSix

end OAI

-- ---- inline helpers from OAI.LinearAlgebra.Hadamard.Polynomials ----
namespace OAI

/-! Fourier kernel identities and symmetric polynomials of row ratios. -/

open scoped BigOperators Matrix

namespace HadamardSix

lemma elementary_eq_sum (v : Index → ℂ) (k : ℕ) :
    elementary v k = ∑ s ∈ Finset.univ.powersetCard k, ∏ i ∈ s, v i :=
  Finset.esymm_map_val v Finset.univ k

lemma elementary_six (v : Index → ℂ) : elementary v 6 = ∏ i, v i := by
  rw [elementary_eq_sum]
  have hcard : (Finset.univ : Finset Index).card = 6 := by decide
  rw [show Finset.univ.powersetCard 6 = ({Finset.univ} : Finset (Finset Index)) by
    simpa only [hcard] using Finset.powersetCard_self (Finset.univ : Finset Index)]
  rw [Finset.sum_singleton]

lemma elementary_two_of_power_sums (v : Index → ℂ)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) : elementary v 2 = 0 := by
  have ha : (Finset.HasAntidiagonal.antidiagonal 2 : Finset (ℕ × ℕ)) =
      {(0, 2), (1, 1), (2, 0)} := by decide
  have hnpoly := MvPolynomial.mul_esymm_eq_sum Index ℂ 2
  rw [ha] at hnpoly
  norm_num [Finset.sum_filter] at hnpoly
  have hn := congrArg (MvPolynomial.aeval v : MvPolynomial Index ℂ →ₐ[ℂ] ℂ) hnpoly
  simp only [map_mul, map_ofNat, map_neg, map_add, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm] at hn
  simp [MvPolynomial.psum, h1, h2] at hn
  exact hn

lemma elementary_complement (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (k : ℕ) (hk : k ≤ 6) :
    elementary v (6 - k) = elementary v 6 * star (elementary v k) := by
  rw [elementary_eq_sum, elementary_six, elementary_eq_sum, star_sum, Finset.mul_sum]
  refine Finset.sum_bij' (fun s _ => sᶜ) (fun s _ => sᶜ) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_powersetCard_univ] at hs ⊢
    rw [Finset.card_compl, Fintype.card_fin, hs, Nat.sub_sub_self hk]
  · intro s hs
    rw [Finset.mem_powersetCard_univ] at hs ⊢
    rw [Finset.card_compl, Fintype.card_fin, hs]
  · intro s hs
    exact compl_compl s
  · intro s hs
    exact compl_compl s
  · intro s hs
    have hunit : ‖∏ i ∈ sᶜ, v i‖ = 1 := by
      simp [norm_prod, hv]
    rw [← Finset.prod_mul_prod_compl s v, mul_assoc, unit_mul_star hunit, mul_one]

end HadamardSix

end OAI

-- ---- hoisted node ----
open OAI OAI.HadamardSix
open scoped BigOperators Matrix

theorem solution (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) : ∑ i, v i ^ 4 = 0 := by
  have ha : (Finset.HasAntidiagonal.antidiagonal 4 : Finset (ℕ × ℕ)) =
      {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} := by decide
  have he4 : elementary v 4 = 0 := by
    simpa only [elementary_two_of_power_sums v h1 h2, star_zero, mul_zero]
      using elementary_complement v hv 2 (by decide)
  have hnpoly := MvPolynomial.mul_esymm_eq_sum Index ℂ 4
  rw [ha] at hnpoly
  norm_num [Finset.sum_filter] at hnpoly
  have hn := congrArg (MvPolynomial.aeval v : MvPolynomial Index ℂ →ₐ[ℂ] ℂ) hnpoly
  simp only [map_mul, map_ofNat, map_neg, map_add, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm] at hn
  have hn' : 4 * elementary v 4 = -(∑ i, v i ^ 4) := by
    simpa [elementary, MvPolynomial.psum, h1, h2] using hn
  rw [he4] at hn'
  simpa using hn'.symm
