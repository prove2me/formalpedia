-- Prove2me | solution 1 for KernelRank.isSumOfProducts_radial_multiComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:41:28.453471+00:00
-- url     : https://prove2.me/submissions/4587459d-fd20-48c1-b987-21deb945fa2c

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_re_coeff_prod_eq_sum_re
import Theorems.Thm_KernelRank_coeff_prod_truncExpPoly
import Theorems.Thm_KernelRank_coeff_revHassePoly_mul_prod_truncExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_natDegree_prod_truncExpPoly_le
import Theorems.Thm_KernelRank_natDegree_revHassePoly_le
import Theorems.Thm_KernelRank_natDegree_truncExpPoly_le
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) {c : Component}
    (hwf : c.WellFormed) :
    IsSumOfProducts (fun x : Fin d → ℝ => c.eval (∑ j, x j ^ 2)) (c.multiCost d) := by
  let k := c.poly.natDegree
  have hd0 : 0 < d := by omega
  let j₀ : Fin d := ⟨0, hd0⟩
  let rest : Finset (Fin d) := Finset.univ.erase j₀
  by_cases him : c.rate.im = 0
  · -- Real rate: Lagrange interpolation over `ℝ` at `0, 1, …, L - 1` (`L = (d - 1) * k + 1`).
    simp only [Component.multiCost, him, ↓reduceIte]
    set L : ℕ := (d - 1) * k + 1
    let P_R : ℝ[X] := ∑ q ∈ Finset.range (k + 1), C (c.poly.coeff q).re * X ^ q
    have hmap_P : P_R.map (algebraMap ℝ ℂ) = c.poly := by
      conv_rhs => rw [as_sum_range' c.poly (k + 1) (Nat.lt_succ_self k)]
      simp only [P_R, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, ← C_mul_X_pow_eq_monomial]
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 2
      exact Complex.ext rfl (hwf.2.2 him q).symm
    have hdeg_PR : P_R.natDegree ≤ k := by
      have : (P_R.map (algebraMap ℝ ℂ)).natDegree = P_R.natDegree :=
        natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective P_R
      rw [← this, hmap_P]
    let truncR (u : ℝ) : ℝ[X] :=
      ∑ q ∈ Finset.range (k + 1), C (u ^ q / (q.factorial : ℝ)) * X ^ q
    have hmap_trunc (u : ℝ) : (truncR u).map (algebraMap ℝ ℂ) = truncExpPoly k (u : ℂ) := by
      simp [truncR, truncExpPoly, Polynomial.map_sum]
    have hdeg_trunc (u : ℝ) : (truncR u).natDegree ≤ k := by
      rw [← natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective (truncR u), hmap_trunc]
      exact natDegree_truncExpPoly_le k (u : ℂ)
    let nodes (r : Fin L) : ℝ := (r : ℕ)
    have hinj_nodes : Set.InjOn nodes ↑(Finset.univ : Finset (Fin L)) := by
      intro a _ b _ hab
      exact Fin.ext (Nat.cast_inj.mp hab)
    let B (r : Fin L) : ℝ[X] := Lagrange.basis Finset.univ nodes r
    let f (r : Fin L) (j : Fin d) (u : ℝ) : ℝ :=
      if j = j₀ then
        (∑ q ∈ Finset.range (k + 1),
          (q.factorial : ℝ) * (B r).coeff q * (hasseDeriv q P_R).eval (u ^ 2)) *
          Real.exp (c.rate.re * u ^ 2)
      else
        (truncR (u ^ 2)).eval (nodes r) * Real.exp (c.rate.re * u ^ 2)
    refine ⟨f, fun x => ?_⟩
    dsimp only
    have heval_c : c.eval (∑ j, x j ^ 2) =
        P_R.eval (∑ j, x j ^ 2) * Real.exp (c.rate.re * ∑ j, x j ^ 2) := by
      have hrate : c.rate = (c.rate.re : ℂ) := Complex.ext rfl (by simpa using him)
      have heval_PR (t : ℝ) : c.poly.eval (t : ℂ) = ((P_R.eval t : ℝ) : ℂ) := by
        rw [← hmap_P]
        simp [P_R, eval_finsetSum]
      unfold Component.eval
      rw [heval_PR, hrate, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      simp only [Complex.ofReal_re]
    let A : ℝ[X] := ∏ j ∈ rest, truncR (x j ^ 2)
    have hdeg_A : A.degree < (Finset.univ : Finset (Fin L)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      refine lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr ?_)
      have hmap_A : A.map (algebraMap ℝ ℂ) = ∏ j ∈ rest, truncExpPoly k (x j ^ 2 : ℂ) := by
        simp [A, Polynomial.map_prod, hmap_trunc]
      have hle : A.natDegree ≤ rest.card * k := by
        rw [← natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective A, hmap_A]
        exact natDegree_prod_truncExpPoly_le rest k (fun j => (x j ^ 2 : ℂ))
      have hcard_rest : rest.card = d - 1 := by simp [rest]
      rw [hcard_rest] at hle
      dsimp [L]; omega
    have hA_interp : A = ∑ r : Fin L, C (A.eval (nodes r)) * B r := by
      have h := Lagrange.eq_interpolate hinj_nodes hdeg_A
      rwa [Lagrange.interpolate_apply] at h
    have hA_coeff (q : ℕ) (hq : q ≤ k) :
        (∑ j ∈ rest, x j ^ 2) ^ q =
          (q.factorial : ℝ) * ∑ r : Fin L, (B r).coeff q * A.eval (nodes r) := by
      have hcC := coeff_prod_truncExpPoly rest k (fun j => (x j ^ 2 : ℂ)) hq
      have hmap_A : A.map (algebraMap ℝ ℂ) = ∏ j ∈ rest, truncExpPoly k (x j ^ 2 : ℂ) := by
        simp [A, Polynomial.map_prod, hmap_trunc]
      have hcast : (∑ j ∈ rest, (x j : ℂ) ^ 2) ^ q / (q.factorial : ℂ) =
          (((∑ j ∈ rest, x j ^ 2) ^ q / (q.factorial : ℝ) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [← hmap_A, coeff_map] at hcC
      have hcC' : (A.coeff q : ℂ) = (((∑ j ∈ rest, x j ^ 2) ^ q / (q.factorial : ℝ) : ℝ) : ℂ) :=
        hcC.trans hcast
      have hcR : A.coeff q = (∑ j ∈ rest, x j ^ 2) ^ q / (q.factorial : ℝ) :=
        Complex.ofReal_inj.mp hcC'
      have hfq : (q.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.factorial_ne_zero
      have hpow : (∑ j ∈ rest, x j ^ 2) ^ q = (q.factorial : ℝ) * A.coeff q := by
        rw [hcR]; field_simp
      conv_lhs => rw [hpow, hA_interp, finsetSum_coeff]
      congr 1
      exact Finset.sum_congr rfl fun r _ => by rw [coeff_C_mul, mul_comm]
    have htaylor : P_R.eval (∑ j : Fin d, x j ^ 2) =
        ∑ q ∈ Finset.range (k + 1),
          (hasseDeriv q P_R).eval (x j₀ ^ 2) * (∑ j ∈ rest, x j ^ 2) ^ q := by
      have hsum_x : x j₀ ^ 2 + ∑ j ∈ rest, x j ^ 2 = ∑ j : Fin d, x j ^ 2 :=
        Finset.add_sum_erase Finset.univ (fun j => x j ^ 2) (Finset.mem_univ j₀)
      rw [← hsum_x, add_comm (x j₀ ^ 2), ← taylor_eval,
        eval_eq_sum_range' (by rw [natDegree_taylor]; exact Nat.lt_succ_of_le hdeg_PR)]
      exact Finset.sum_congr rfl fun q _ => by rw [taylor_coeff]
    have hPR_sum : P_R.eval (∑ j : Fin d, x j ^ 2) =
        ∑ r : Fin L,
          (∑ q ∈ Finset.range (k + 1),
            (q.factorial : ℝ) * (B r).coeff q * (hasseDeriv q P_R).eval (x j₀ ^ 2)) *
          ∏ j ∈ rest, (truncR (x j ^ 2)).eval (nodes r) := by
      rw [htaylor]
      have hstep : ∑ q ∈ Finset.range (k + 1),
          (hasseDeriv q P_R).eval (x j₀ ^ 2) * (∑ j ∈ rest, x j ^ 2) ^ q =
          ∑ q ∈ Finset.range (k + 1), ∑ r : Fin L,
            (q.factorial : ℝ) * (B r).coeff q * (hasseDeriv q P_R).eval (x j₀ ^ 2) *
              A.eval (nodes r) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [hA_coeff q (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)),
          ← mul_assoc, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [hstep, Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_mul, eval_prod]
    rw [heval_c, hPR_sum, Finset.sum_mul, Finset.mul_sum, Real.exp_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    conv_lhs =>
      rw [← Finset.mul_prod_erase Finset.univ (fun j => Real.exp (c.rate.re * x j ^ 2))
        (Finset.mem_univ j₀)]
    conv_rhs =>
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
    have her : ∏ j ∈ rest, f r j (x j) =
        (∏ j ∈ rest, (truncR (x j ^ 2)).eval (nodes r)) *
          ∏ j ∈ rest, Real.exp (c.rate.re * x j ^ 2) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j hj => by simp [f, Finset.ne_of_mem_erase hj]
    rw [her]
    simp only [f, ↓reduceIte]
    ring
  · -- Nonreal rate: apply `re_coeff_prod_eq_sum_re` with `R = 2 * (d - 1) * k + d`.
    simp only [Component.multiCost, him, ↓reduceIte]
    set R : ℕ := 2 * (d - 1) * k + d
    let U_of (x : ℝ) (j : Fin d) : ℂ[X] :=
      C (exp (c.rate * (x ^ 2 : ℝ))) *
        if j = j₀ then revHassePoly c.poly k (x ^ 2 : ℝ) else truncExpPoly k (x ^ 2 : ℝ)
    let ζ (r : Fin R) : ℂ := exp (2 * Real.pi * I * (r : ℕ) / R)
    let rot (r : Fin R) : ℂ := exp (-Real.pi * I * (r : ℕ) * (2 * k + 1 : ℕ) / R)
    let f (r : Fin R) (j : Fin d) (u : ℝ) : ℝ :=
      if j = j₀ then
        (2 : ℝ) ^ (d - 1) / R * (-1 : ℝ) ^ (r : ℕ) * ((U_of u j).eval (ζ r) * rot r).re
      else
        ((U_of u j).eval (ζ r) * rot r).re
    refine ⟨f, fun x => ?_⟩
    dsimp only
    have hdeg_U (j : Fin d) : (U_of (x j) j).natDegree ≤ k := by
      dsimp [U_of]
      refine natDegree_C_mul_le _ _ |>.trans ?_
      split_ifs
      · exact natDegree_revHassePoly_le c.poly k (x j ^ 2 : ℝ)
      · exact natDegree_truncExpPoly_le k (x j ^ 2 : ℝ)
    have hprod_U : ((∏ j : Fin d, U_of (x j) j).coeff k).re = c.eval (∑ j, x j ^ 2) := by
      have hpull_C : (∏ j : Fin d, U_of (x j) j) =
          C (exp (c.rate * (∑ j : Fin d, x j ^ 2 : ℝ))) *
            (revHassePoly c.poly k (x j₀ ^ 2 : ℝ) *
              ∏ j ∈ rest, truncExpPoly k (x j ^ 2 : ℝ)) := by
        dsimp [U_of]
        rw [Finset.prod_mul_distrib, ← map_prod C, ← Complex.exp_sum, ← Finset.mul_sum,
          ← Complex.ofReal_sum]
        congr 1
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
        simp only [↓reduceIte]
        congr 1
        exact Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
      rw [hpull_C, coeff_C_mul,
        coeff_revHassePoly_mul_prod_truncExpPoly c.poly j₀ (fun j => ((x j ^ 2 : ℝ) : ℂ))]
      simp only [Component.eval, Complex.ofReal_sum, mul_comm]
    rw [← hprod_U, re_coeff_prod_eq_sum_re hd k (fun j => U_of (x j) j) hdeg_U, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    conv_lhs =>
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => ((U_of (x j) j).eval (ζ r) * rot r).re) (Finset.mem_univ j₀)]
    conv_rhs =>
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
    have her : ∏ j ∈ rest, f r j (x j) =
        ∏ j ∈ rest, ((U_of (x j) j).eval (ζ r) * rot r).re :=
      Finset.prod_congr rfl fun j hj => by simp [f, Finset.ne_of_mem_erase hj]
    rw [her]
    simp only [f, ↓reduceIte]
    ring
end KernelRank
