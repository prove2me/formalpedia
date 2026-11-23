-- Prove2me | solution 1 for KernelRank.isSumOfProducts_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:40:39.956237+00:00
-- url     : https://prove2.me/submissions/bff74dc1-0679-4580-9731-a6057910b9e1

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_coeff_eq_sum_rootsOfUnity
import Theorems.Thm_KernelRank_natDegree_prod_truncExpPoly_le
import Theorems.Thm_KernelRank_natDegree_revHassePoly_le
import Theorems.Thm_KernelRank_coeff_revHassePoly_mul_prod_truncExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (P : ℂ[X]) (μ : ℂ) :
    IsSumOfProducts (fun s : Fin d → ℝ≥0 => expPoly P μ (∑ j, (s j : ℝ)))
      ((d - 1) * P.natDegree + 1) := by
  let k := P.natDegree
  let L := (d - 1) * k + 1
  have hd0 : 0 < d := by omega
  let j₀ : Fin d := ⟨0, hd0⟩
  let rest : Finset (Fin d) := Finset.univ.erase j₀
  have hcard : rest.card = d - 1 := by simp [rest]
  let ζ (r : Fin L) : ℂ := exp (2 * Real.pi * I * (r : ℕ) / L)
  let f (r : Fin L) (j : Fin d) (u : ℝ≥0) : ℂ :=
    if j = j₀ then
      (L : ℂ)⁻¹ * exp (-2 * Real.pi * I * k * (r : ℕ) / L) *
        (revHassePoly P k (u : ℂ)).eval (ζ r) * exp (μ * u)
    else
      (truncExpPoly k (u : ℂ)).eval (ζ r) * exp (μ * u)
  refine ⟨f, fun s => ?_⟩
  let Q : ℂ[X] := revHassePoly P k (s j₀ : ℂ) * ∏ j ∈ rest, truncExpPoly k (s j : ℂ)
  have hdegQ : Q.natDegree < k + L := by
    have hle : Q.natDegree ≤ k + (d - 1) * k := by
      refine natDegree_mul_le.trans ?_
      have h1 := natDegree_revHassePoly_le P k (s j₀ : ℂ)
      have h2 := natDegree_prod_truncExpPoly_le rest k (fun j => (s j : ℂ))
      rw [hcard] at h2
      linarith
    have : k + (d - 1) * k < k + L := by dsimp [L]; omega
    exact lt_of_le_of_lt hle this
  have hkL : k < L := by
    have : 1 * k ≤ (d - 1) * k := Nat.mul_le_mul_right k (by omega)
    dsimp [L]
    omega
  have hcoeffQ : Q.coeff k = P.eval (∑ j : Fin d, (s j : ℂ)) :=
    coeff_revHassePoly_mul_prod_truncExpPoly P j₀ (fun j => (s j : ℂ))
  have hroots := coeff_eq_sum_rootsOfUnity Q hkL hdegQ
  rw [hcoeffQ, ← Fin.sum_univ_eq_sum_range] at hroots
  simp only [expPoly, Complex.ofReal_sum, hroots, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hprod_exp : exp (∑ j : Fin d, μ * (s j : ℂ)) = ∏ j : Fin d, exp (μ * (s j : ℂ)) :=
    Complex.exp_sum _ _
  have hsplit := (Finset.mul_prod_erase Finset.univ (fun j => f r j (s j))
    (Finset.mem_univ j₀)).symm
  have hsplit_exp := (Finset.mul_prod_erase Finset.univ (fun j => exp (μ * (s j : ℂ)))
    (Finset.mem_univ j₀)).symm
  rw [hsplit, hprod_exp, hsplit_exp]
  have hf0 : f r j₀ (s j₀) =
      (L : ℂ)⁻¹ * exp (-2 * Real.pi * I * k * (r : ℕ) / L) *
        (revHassePoly P k (s j₀ : ℂ)).eval (ζ r) * exp (μ * (s j₀ : ℂ)) := by
    simp [f]
  have hfrest : ∏ j ∈ rest, f r j (s j) =
      (∏ j ∈ rest, (truncExpPoly k (s j : ℂ)).eval (ζ r)) *
        ∏ j ∈ rest, exp (μ * (s j : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j hj => by
      simp [f, Finset.ne_of_mem_erase hj]
  have hevalQ : Q.eval (ζ r) =
      (revHassePoly P k (s j₀ : ℂ)).eval (ζ r) *
        ∏ j ∈ rest, (truncExpPoly k (s j : ℂ)).eval (ζ r) := by
    simp [Q, eval_mul, eval_prod]
  rw [hf0, hfrest, hevalQ]
  ring
end KernelRank
