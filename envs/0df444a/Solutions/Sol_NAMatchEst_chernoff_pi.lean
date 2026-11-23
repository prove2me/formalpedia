-- Prove2me | solution 1 for NAMatchEst.chernoff_pi
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:29:18.002387+00:00
-- url     : https://prove2.me/submissions/84281b30-7c87-49f0-a5ed-416df7c052df

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_RandomQueryXOR_uniformOn




namespace NAMatchEst.AuxChernoff

open WildeQIT

lemma exp_mul_le (s x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp (s * x) ≤ 1 + x * (Real.exp s - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ s) (by linarith : (0:ℝ) ≤ 1 - x)
    h0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc Real.exp (s * x) = Real.exp (x * s) := by rw [mul_comm]
    _ ≤ 1 - x + x * Real.exp s := h
    _ = 1 + x * (Real.exp s - 1) := by ring

lemma mgf_eq {m : ℕ} {Q : Type} [Fintype Q] (p : Fin m → FinDist Q) (f : Fin m → Q → ℝ) (s : ℝ) :
    ∑ ω, (RandomQueryXOR.piDist p).prob ω * Real.exp (s * ∑ i, f i (ω i)) =
      ∏ i, ∑ q, (p i).prob q * Real.exp (s * f i q) := by
  rw [Fintype.prod_sum (fun i q => (p i).prob q * Real.exp (s * f i q))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [RandomQueryXOR.piDist]
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]

lemma coord_le {Q : Type} [Fintype Q] (p : FinDist Q) (g : Q → ℝ) (hg : ∀ q, 0 ≤ g q ∧ g q ≤ 1)
    (s : ℝ) :
    ∑ q, p.prob q * Real.exp (s * g q) ≤ Real.exp ((∑ q, p.prob q * g q) * (Real.exp s - 1)) := by
  calc ∑ q, p.prob q * Real.exp (s * g q)
      ≤ ∑ q, p.prob q * (1 + g q * (Real.exp s - 1)) :=
        Finset.sum_le_sum fun q _ =>
          mul_le_mul_of_nonneg_left (exp_mul_le s (g q) (hg q).1 (hg q).2) (p.nonneg q)
    _ = (∑ q, p.prob q * g q) * (Real.exp s - 1) + 1 := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, p.sum_eq_one, Finset.sum_mul]
        rw [add_comm]
        congr 1
        exact Finset.sum_congr rfl fun q _ => by ring
    _ ≤ _ := Real.add_one_le_exp _

lemma mgf_le {m : ℕ} {Q : Type} [Fintype Q] (p : Fin m → FinDist Q) (f : Fin m → Q → ℝ)
    (hf : ∀ i q, 0 ≤ f i q ∧ f i q ≤ 1) (s : ℝ) :
    ∑ ω, (RandomQueryXOR.piDist p).prob ω * Real.exp (s * ∑ i, f i (ω i)) ≤
      Real.exp ((∑ i, ∑ q, (p i).prob q * f i q) * (Real.exp s - 1)) := by
  rw [mgf_eq, Finset.sum_mul, Real.exp_sum]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => coord_le (p i) (f i) (hf i) s)
  exact Finset.sum_nonneg fun q _ => mul_nonneg ((p i).nonneg q) (Real.exp_pos _).le

end NAMatchEst.AuxChernoff

open NAMatchEst.AuxChernoff in
theorem solution {m : ℕ} {Q : Type} [Fintype Q] (p : Fin m → WildeQIT.FinDist Q)
    (f : Fin m → Q → ℝ) (hf : ∀ i q, 0 ≤ f i q ∧ f i q ≤ 1) (lamL lamH t a : ℝ)
    (hL : lamL ≤ ∑ i, ∑ q, (p i).prob q * f i q) (hH : ∑ i, ∑ q, (p i).prob q * f i q ≤ lamH)
    (ht : 0 ≤ t) :
    (∑ ω, (RandomQueryXOR.piDist p).prob ω * if a ≤ ∑ i, f i (ω i) then 1 else 0) ≤
        Real.exp (lamH * (Real.exp t - 1) - t * a) ∧
      (∑ ω, (RandomQueryXOR.piDist p).prob ω * if ∑ i, f i (ω i) ≤ a then 1 else 0) ≤
        Real.exp (lamL * (Real.exp (-t) - 1) + t * a) := by
  set μ := ∑ i, ∑ q, (p i).prob q * f i q with hμ
  constructor
  · calc (∑ ω, (RandomQueryXOR.piDist p).prob ω * if a ≤ ∑ i, f i (ω i) then 1 else 0)
        ≤ ∑ ω, (RandomQueryXOR.piDist p).prob ω *
            (Real.exp (-(t * a)) * Real.exp (t * ∑ i, f i (ω i))) := by
          refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_
            ((RandomQueryXOR.piDist p).nonneg ω)
          rw [← Real.exp_add]
          split_ifs with h
          · exact Real.one_le_exp (by nlinarith)
          · exact (Real.exp_pos _).le
      _ = Real.exp (-(t * a)) *
            ∑ ω, (RandomQueryXOR.piDist p).prob ω * Real.exp (t * ∑ i, f i (ω i)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ Real.exp (-(t * a)) * Real.exp (μ * (Real.exp t - 1)) :=
          mul_le_mul_of_nonneg_left (mgf_le p f hf t) (Real.exp_pos _).le
      _ ≤ Real.exp (lamH * (Real.exp t - 1) - t * a) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          have : 0 ≤ Real.exp t - 1 := by linarith [Real.one_le_exp ht]
          nlinarith
  · calc (∑ ω, (RandomQueryXOR.piDist p).prob ω * if ∑ i, f i (ω i) ≤ a then 1 else 0)
        ≤ ∑ ω, (RandomQueryXOR.piDist p).prob ω *
            (Real.exp (t * a) * Real.exp (-t * ∑ i, f i (ω i))) := by
          refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_
            ((RandomQueryXOR.piDist p).nonneg ω)
          rw [← Real.exp_add]
          split_ifs with h
          · exact Real.one_le_exp (by nlinarith)
          · exact (Real.exp_pos _).le
      _ = Real.exp (t * a) *
            ∑ ω, (RandomQueryXOR.piDist p).prob ω * Real.exp (-t * ∑ i, f i (ω i)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ Real.exp (t * a) * Real.exp (μ * (Real.exp (-t) - 1)) :=
          mul_le_mul_of_nonneg_left (mgf_le p f hf (-t)) (Real.exp_pos _).le
      _ ≤ Real.exp (lamL * (Real.exp (-t) - 1) + t * a) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          have : Real.exp (-t) - 1 ≤ 0 := by
            linarith [Real.exp_le_one_iff.2 (by linarith : -t ≤ 0)]
          nlinarith
