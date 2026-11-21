-- Prove2me | solution 1 for MomentSearch.Supplement.theorem_20
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:22:24.939455+00:00
-- url     : https://prove2.me/submissions/fa9278c8-d959-4fd3-966e-cec120ffa7e3

import Mathlib
import Definitions.Def_MomentSearch_approxFactor
import Definitions.Def_MomentSearch_sketchCollection
import Theorems.Thm_MomentSearch_kraft_average_depth
import Theorems.Thm_MomentSearch_Supplement_sparse_support_opt_upper_bound
open MomentSearch MomentSearch.Supplement
open scoped BigOperators ENNReal

private lemma sparse_convex_combination {n d : ℕ} (v : Fin n → (Fin d → ℝ))
    (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    ∃ r ∈ stdSimplex ℝ (Fin n), (Function.support r).ncard ≤ d+1 ∧
      ∑ t : Fin n, r t • v t = ∑ t : Fin n, p t • v t := by
  classical
  have hx : (∑ t : Fin n, p t • v t) ∈ convexHull ℝ (Set.range v) :=
    mem_convexHull_of_exists_fintype p v hp.1 hp.2 (fun t => ⟨t,rfl⟩) rfl
  obtain ⟨ι, inst, z, w, hz, hi, hw, hsum, heq⟩ := eq_pos_convex_span_of_mem_convexHull hx
  let := inst
  have hpre (i : ι) : ∃ t, v t = z i := hz ⟨i,rfl⟩
  choose idx hidx using hpre
  let r : Fin n → ℝ := fun t => ∑ i : ι, if idx i = t then w i else 0
  have hrnon : ∀ t, 0 ≤ r t := by
    intro t
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> [exact (hw i).le; rfl]
  have hrmass : ∑ t : Fin n, r t = 1 := by
    dsimp [r]
    rw [Finset.sum_comm]
    simpa using hsum
  have hsub : Function.support r ⊆ Set.range idx := by
    intro t ht
    by_contra hh
    have hne : ∀ i, idx i ≠ t := by simpa using hh
    have hz : r t = 0 := by simp [r, hne]
    exact ht hz
  have hcard : (Function.support r).ncard ≤ Fintype.card ι := by
    calc
      _ ≤ (Set.range idx).ncard := Set.ncard_le_ncard hsub (Set.finite_range idx)
      _ ≤ Fintype.card ι := by
        have hc := Set.ncard_image_le (s:=Set.univ) (f:=idx)
        simpa [Set.image_univ, Set.ncard_univ, Nat.card_eq_fintype_card] using hc
  have hdim : Fintype.card ι ≤ d+1 := by
    have hf : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ d := by
      simpa using (Submodule.finrank_le (vectorSpan ℝ (Set.range z)))
    exact hi.card_le_finrank_succ.trans (Nat.add_le_add_right hf 1)
  refine ⟨r, ⟨hrnon,hrmass⟩, hcard.trans hdim, ?_⟩
  calc
    _ = ∑ i : ι, w i • v (idx i) := by
      simp only [r, Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [ite_smul, zero_smul]
      simp
    _ = ∑ i : ι, w i • z i := by simp only [hidx]
    _ = _ := heq

private lemma sparse_fibre_cost {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) (c : Fin n → ℝ) :
    ∃ r ∈ stdSimplex ℝ (Fin n), (Function.support r).ncard ≤ k+2 ∧
      Matrix.mulVec A r = Matrix.mulVec A p ∧ (∑ t, r t*c t) = ∑ t, p t*c t := by
  let v : Fin n → (Fin (k+1) → ℝ) := fun t => Fin.lastCases (c t) (fun i => A i t)
  obtain ⟨r, hr, hcard, heq⟩ := sparse_convex_combination v p hp
  refine ⟨r, hr, hcard, ?_, ?_⟩
  · ext i
    have hh := congrFun heq i.castSucc
    simpa [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, mul_comm] using hh
  · have hh := congrFun heq (Fin.last k)
    simpa [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh

private lemma uniform_simplex {n : ℕ} (hn : 0 < n) :
    (fun _ : Fin n => (1:ℝ)/n) ∈ stdSimplex ℝ (Fin n) := by
  refine ⟨fun t => by positivity, ?_⟩
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [hn0]

private lemma uniform_cost_lower {n : ℕ} (hn : 2 ≤ n) (S : Strategy n) :
    Real.logb 2 n / 2 ≤ cost (fun _ : Fin n => (1:ℝ)/n) S := by
  have hkraft : Real.logb 3 n ≤ cost (fun _ : Fin n => (1:ℝ)/n) S := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hh := (MomentSearch.kraft_average_depth hn S m (fun t => t) Function.injective_id).2
    simpa [cost, ← Finset.mul_sum, Nat.cast_add, Nat.cast_one] using hh
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hL3 : 0 ≤ Real.logb 3 n := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (by omega : 1≤n))
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<3) (by norm_num : (3:ℝ)≤2^2)
    simpa [Real.log_pow] using hh
  have heq : Real.logb 2 n * Real.log 2 = Real.logb 3 n * Real.log 3 := by
    unfold Real.logb
    field_simp
  have hrel : Real.logb 2 n / 2 ≤ Real.logb 3 n := by
    nlinarith [mul_le_mul_of_nonneg_left hlog3 hL3]
  exact hrel.trans hkraft

private lemma sparse_opt_log {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (hs : (Function.support p).ncard ≤ k+2) :
    0 < OPT p ∧ OPT p ≤ 3 * Real.logb 2 k := by
  obtain ⟨hpos, hu⟩ := sparse_support_opt_upper_bound hn (by omega : 0 < k+2) p hp hs
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hL : 1 ≤ Real.logb 2 k := by
    simpa using Real.logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) hkR
  have hsq : (k:ℝ)+2 ≤ (k:ℝ)^2 := by nlinarith
  have hh := Real.logb_le_logb_of_le (b:=2) (by norm_num) (by positivity : 0 < (k:ℝ)+2) hsq
  rw [Real.logb_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  push_cast at hu
  exact ⟨hpos, by linarith⟩

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ (k : ℕ), 2 ≤ k → ∀ A : Matrix (Fin k) (Fin n) ℝ,
        ENNReal.ofReal (c * Real.logb 2 n / Real.logb 2 k) ≤
          approxFactor (sketchCollection (fun p : Fin n → ℝ => Matrix.mulVec A p)) := by
  classical
  refine ⟨1/6, by norm_num, ?_⟩
  intro n hn k hk A
  let u : Fin n → ℝ := fun _ => 1/(n:ℝ)
  have hu : u ∈ stdSimplex ℝ (Fin n) := uniform_simplex (by omega)
  let U := {p : Fin n → ℝ | p ∈ stdSimplex ℝ (Fin n) ∧ Matrix.mulVec A p = Matrix.mulVec A u}
  have hU : U ∈ sketchCollection (fun p : Fin n → ℝ => Matrix.mulVec A p) :=
    ⟨⟨u,hu,rfl⟩, Matrix.mulVec A u, rfl⟩
  unfold approxFactor
  apply le_iSup_of_le U
  apply le_iSup_of_le hU
  apply le_iInf
  intro S
  obtain ⟨p, hp, hs, hA, hc⟩ := sparse_fibre_cost A u hu (fun t => (queries S t.val : ℝ))
  have hcost : Real.logb 2 n / 2 ≤ cost p S := by
    change cost p S = cost u S at hc
    rw [hc]
    exact uniform_cost_lower hn S
  obtain ⟨hopt, hupper⟩ := sparse_opt_log hn hk p hp hs
  apply le_iSup_of_le p
  apply le_iSup_of_le (show p ∈ U from ⟨hp,hA⟩)
  apply ENNReal.ofReal_le_ofReal
  have hnlog : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (by omega : 1≤n))
  have hklog : 0 < Real.logb 2 k := Real.logb_pos (by norm_num)
    (by exact_mod_cast (by omega : 1<k))
  apply (le_div_iff₀ hopt).2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hklog).2
  nlinarith [mul_le_mul_of_nonneg_left hupper hnlog,
    mul_le_mul_of_nonneg_right hcost hklog.le]
