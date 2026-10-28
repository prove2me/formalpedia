-- Prove2me | solution 2 for LeightonRao.BadExample.flow_le_of_expander
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:22.910502+00:00
-- url     : https://prove2.me/submissions/20ea4852-56b1-4d9b-9e82-2e1d950d968a

import Mathlib
import Definitions.Def_LeightonRao_BadExample_Setting
import Theorems.Thm_LeightonRao_BadExample_half_pairs_far
import Theorems.Thm_LeightonRao_BadExample_min_cut_ge

-- carved verbatim out of submission 669bd3d3-6598-48ea-81a3-0336aa8b2e1d, lines 390-411

section
set_option autoImplicit false
open scoped BigOperators
open LeightonRao.BadExample
set_option maxHeartbeats 1000000

private noncomputable def clipped {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : V) (r : ℕ) (v : V) : ℕ :=
  (min (G.edist s v) (r : ℕ∞)).toNat

private lemma clipped_source {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : V) (r : ℕ) : clipped G s r s = 0 := by
  simp [clipped]

private lemma clipped_far {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s t : V) (r : ℕ) (h : (r : ℕ∞) ≤ G.edist s t) :
    clipped G s r t = r := by simp [clipped, min_eq_right h]

private lemma clipped_adj {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s i j : V) (r : ℕ) (hij : G.Adj i j) :
    clipped G s r j ≤ clipped G s r i + 1 := by
  have hj : G.edist s j ≤ G.edist s i + 1 := by
    simpa [G.edist_eq_one_iff_adj.mpr hij] using (G.edist_triangle (u:=s) (v:=i) (w:=j))
  have hi : G.edist s i ≤ G.edist s j + 1 := by
    simpa [G.edist_eq_one_iff_adj.mpr hij.symm] using (G.edist_triangle (u:=s) (v:=j) (w:=i))
  generalize he1 : G.edist s i = di at *
  generalize he2 : G.edist s j = dj at *
  unfold clipped
  rw [he1, he2]
  cases di using ENat.recTopCoe <;> cases dj using ENat.recTopCoe
  · simp
  · simp at hi
  · simp at hj
  · try simp only [← ENat.natCast_add, ENat.natCast_le_natCast] at hj hi
    rename_i a b
    have hmin (a b : ℕ) : (min (a : ℕ∞) (b : ℕ∞)).toNat = min a b := by
      rcases le_total a b with hab | hba
      · simp [min_eq_left hab, min_eq_left (by exact_mod_cast hab : (a : ℕ∞) ≤ b)]
      · simp [min_eq_right hba, min_eq_right (by exact_mod_cast hba : (b : ℕ∞) ≤ a)]
    rw [hmin, hmin]
    norm_cast at hj hi
    omega

private lemma commodity_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → V → V → V → ℝ) (lam : ℝ)
    (hf : IsConcurrentFlow (unitNetwork G) uniformDemand f lam)
    (s t : V) (hst : s ≠ t) (r : ℕ) (hfar : (r : ℕ∞) ≤ G.edist s t) :
    lam / 2 * r ≤ ∑ i, ∑ j, f s t i j := by
  classical
  let d : V → ℝ := fun v => (clipped G s r v : ℝ)
  have hzero (i j : V) (hij : ¬ G.Adj i j) : f s t i j = 0 := by
    have hc := hf.2.2.2 i j
    have h1 : f s t i j + f s t j i ≤ ∑ s, ∑ t, (f s t i j + f s t j i) := by
      exact (Finset.single_le_sum (fun t _ => add_nonneg (hf.1 s t i j) (hf.1 s t j i)) (Finset.mem_univ t)).trans
        (Finset.single_le_sum (fun s _ => Finset.sum_nonneg fun t _ => add_nonneg (hf.1 s t i j) (hf.1 s t j i)) (Finset.mem_univ s))
    simp only [unitNetwork, hij, if_false] at hc
    linarith [hf.1 s t i j, hf.1 s t j i]
  have hd (i j : V) : f s t i j * (d j-d i) ≤ f s t i j := by
    by_cases hij : G.Adj i j
    · have hh : d j-d i ≤ 1 := by
        have hh : (clipped G s r j : ℝ) ≤ (clipped G s r i : ℝ) + 1 := by exact_mod_cast clipped_adj G s i j r hij
        dsimp [d]; linarith
      nlinarith [hf.1 s t i j]
    · simp [hzero i j hij]
  have hb : (∑ i, d i * ((∑ j, f s t j i) - (∑ j, f s t i j))) = lam / 2 * r := by
    simp_rw [show ∀ i, (∑ j, f s t j i) - (∑ j, f s t i j) =
      -(lam * uniformDemand s t * ((if i=s then 1 else 0)-(if i=t then 1 else 0))) by
        intro i; have h := hf.2.1 s t hst i; linarith]
    simp only [uniformDemand, hst, if_false]
    simp only [mul_neg, neg_sub, mul_sub, Finset.sum_sub_distrib]
    simp [d, clipped_source, clipped_far G s t r hfar, mul_comm, mul_left_comm, mul_assoc]
    ring
  have he : (∑ i, d i * ((∑ j, f s t j i) - (∑ j, f s t i j))) =
      ∑ i, ∑ j, f s t i j * (d j-d i) := by
    simp_rw [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f:=fun i j => d i * f s t j i)]
    simp only [mul_comm]
  rw [← hb, he]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hd i j

private lemma swap4 {V : Type} [Fintype V]
    (g : V → V → V → V → ℝ) :
    (∑ s, ∑ t, ∑ i, ∑ j, g s t i j) = ∑ i, ∑ j, ∑ s, ∑ t, g s t i j := by
  calc
    _ = ∑ s, ∑ i, ∑ t, ∑ j, g s t i j := by
      apply Finset.sum_congr rfl; intro s _; exact Finset.sum_comm
    _ = ∑ i, ∑ s, ∑ t, ∑ j, g s t i j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro i _
      calc
        _ = ∑ s, ∑ j, ∑ t, g s t i j := by
          apply Finset.sum_congr rfl; intro s _; exact Finset.sum_comm
        _ = _ := Finset.sum_comm

private lemma feasible_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hn : 8 ≤ Fintype.card V)
    (f : V → V → V → V → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hf : IsConcurrentFlow (unitNetwork G) uniformDemand f lam) :
    lam ≤ 6 / (((Fintype.card V : ℝ)-1) * ((Nat.log 2 (Fintype.card V) : ℝ)-2)) := by
  classical
  let n := Fintype.card V
  let r := Nat.log 2 n - 2
  let F : Finset (V × V) := Finset.univ.filter (fun p => (r : ℕ∞) ≤ G.edist p.1 p.2)
  let T : ℝ := ∑ s, ∑ t, ∑ i, ∑ j, f s t i j
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 3 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hr : 0 < r := by dsimp [r]; omega
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hre : (r : ℝ) = (Nat.log 2 n : ℝ)-2 := by dsimp [r]; rw [Nat.cast_sub (by omega)]; norm_num
  have hfar : (n : ℝ)^2/2 ≤ (F.card : ℝ) := LeightonRao.BadExample.half_pairs_far G h3 hn
  have hF : (F.card : ℝ) * (lam/2*r) ≤ T := by
    calc
      _ = ∑ p ∈ F, lam/2*r := by simp [mul_comm]
      _ ≤ ∑ p ∈ F, ∑ i, ∑ j, f p.1 p.2 i j := by
        apply Finset.sum_le_sum
        intro p hp
        have hd := (Finset.mem_filter.mp hp).2
        have hst : p.1 ≠ p.2 := by
          intro he
          rw [he] at hd
          simp only [SimpleGraph.edist_self] at hd
          have : r ≤ 0 := by exact_mod_cast hd
          omega
        exact commodity_bound G f lam hf p.1 p.2 hst r hd
      _ ≤ ∑ p : V × V, ∑ i, ∑ j, f p.1 p.2 i j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro p _ _
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hf.1 _ _ i j
      _ = T := by simp only [Fintype.sum_prod_type]; rfl
  have hcap : 2*T ≤ 3*(n:ℝ) := by
    have hc := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset V)) =>
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset V)) => hf.2.2.2 i j))
    have hrow (i : V) : (∑ j, (unitNetwork G).C i j) = 3 := by
      change (∑ j, if G.Adj i j then (1:ℝ) else 0) = 3
      have he : (∑ j, if G.Adj i j then (1:ℝ) else 0) = (G.degree i : ℝ) := by
        simp [SimpleGraph.degree, SimpleGraph.neighborFinset]
      rw [he, h3.degree_eq i]; norm_num
    have he : (∑ i, ∑ j, ∑ s, ∑ t, (f s t i j + f s t j i)) = 2*T := by
      simp_rw [Finset.sum_add_distrib]
      have hh : (∑ i, ∑ j, ∑ s, ∑ t, f s t j i) = ∑ i, ∑ j, ∑ s, ∑ t, f s t i j := Finset.sum_comm
      rw [hh, ← swap4]
      dsimp [T]; ring
    rw [he] at hc
    simp_rw [hrow] at hc
    simpa [n, mul_comm] using hc
  have hlower := mul_le_mul_of_nonneg_right hfar (show 0 ≤ lam/2*(r:ℝ) by positivity)
  have ht : (n:ℝ)^2/2 * (lam/2*r) ≤ T := hlower.trans hF
  have hnpos : 0 < (n:ℝ) := by linarith
  have hprod : lam * (n:ℝ) * (r:ℝ) ≤ 6 := by
    have hh : (n:ℝ) * (lam*(n:ℝ)*(r:ℝ)-6) ≤ 0 := by nlinarith
    by_contra h
    have hp := mul_pos hnpos (show 0 < lam*(n:ℝ)*(r:ℝ)-6 by linarith)
    linarith
  rw [← hre]
  have hnm : 0 < (n:ℝ)-1 := by linarith
  apply (le_div_iff₀ (show 0 < ((n:ℝ)-1)*(r:ℝ) by positivity)).2
  have hh : 0 ≤ lam*(r:ℝ) := mul_nonneg hlam hrR.le
  nlinarith

private theorem max_flow_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3)
    (hn : 8 ≤ Fintype.card V) :
    maxFlow (unitNetwork G) uniformDemand ≤
      6 / (((Fintype.card V : ℝ) - 1) * ((Nat.log 2 (Fintype.card V) : ℝ) - 2)) := by
  have hnR : (8 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlog : 3 ≤ Nat.log 2 (Fintype.card V) := Nat.le_log_of_pow_le (by norm_num) hn
  have hlogR : (3 : ℝ) ≤ Nat.log 2 (Fintype.card V) := by exact_mod_cast hlog
  apply csSup_le
  · refine ⟨0, le_rfl, (fun _ _ _ _ => 0), ?_⟩
    simp [IsConcurrentFlow]
    exact (unitNetwork G).C_nonneg
  · rintro lam ⟨hlam, f, hf⟩
    exact feasible_bound G h3 hn f lam hlam hf

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3)
    (c : ℝ) (hc : 0 < c) (hexp : IsEdgeExpander G c)
    (hn : 8 ≤ Fintype.card V) :
    maxFlow (unitNetwork G) uniformDemand ≤
      6 * minCut (unitNetwork G) /
        (c * ((Nat.log 2 (Fintype.card V) : ℝ) - 2)) := by
  have hflow := max_flow_le G h3 hn
  have hcut := LeightonRao.BadExample.min_cut_ge G c hc hexp (by omega)
  have hnR : (8 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlog : 3 ≤ Nat.log 2 (Fintype.card V) := Nat.le_log_of_pow_le (by norm_num) hn
  have hlogR : (3 : ℝ) ≤ Nat.log 2 (Fintype.card V) := by exact_mod_cast hlog
  have hnpos : 0 < (Fintype.card V : ℝ)-1 := by linarith
  have hrpos : 0 < (Nat.log 2 (Fintype.card V) : ℝ)-2 := by linarith
  apply hflow.trans
  rw [div_le_div_iff₀ (mul_pos hnpos hrpos) (mul_pos hc hrpos)]
  have hcut' := (div_le_iff₀ hnpos).mp hcut
  nlinarith [mul_le_mul_of_nonneg_right hcut' hrpos.le]

end
