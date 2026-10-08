-- Prove2me | solution 1 for LeightonRao.BadExample.flow_le_of_expander
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:28:14.512287+00:00
-- url     : https://prove2.me/submissions/669bd3d3-6598-48ea-81a3-0336aa8b2e1d

import Mathlib
import Definitions.Def_LeightonRao_BadExample_Setting
set_option autoImplicit false
open scoped BigOperators
open LeightonRao.BadExample
set_option maxHeartbeats 1000000

private lemma predecessor {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (r : ℕ)
    (hu : G.edist v u = ((r+1 : ℕ) : ℕ∞)) :
    ∃ w, G.Adj u w ∧ G.edist v w = (r : ℕ∞) := by
  obtain ⟨p, hp⟩ := G.exists_walk_of_edist_eq_coe (G.edist_comm.trans hu)
  cases p with
  | nil => simp at hp
  | @cons u w z hadj tail =>
    have hlen : tail.length = r := by simp only [SimpleGraph.Walk.length_cons] at hp; omega
    have hle : G.edist v w ≤ (r : ℕ∞) := by
      simpa [hlen, G.edist_comm] using tail.edist_le
    have htri : G.edist v u ≤ G.edist v w + G.edist w u := G.edist_triangle
    rw [hu, G.edist_eq_one_iff_adj.mpr hadj.symm] at htri
    have hfinite : G.edist v w ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hle (ENat.natCast_lt_top r))
    lift G.edist v w to ℕ using hfinite with q hq
    have hqle : q ≤ r := by exact_mod_cast hle
    have hqge : r+1 ≤ q+1 := by exact_mod_cast htri
    have : q = r := by omega
    exact ⟨w, hadj, by simpa [this] using hq.symm⟩

private noncomputable def sphere {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => G.edist v u = (r : ℕ∞))

private lemma sphere_step {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3)
    (v : V) (r : ℕ) (hr : 1 ≤ r) :
    (sphere G v (r+1)).card ≤ 2 * (sphere G v r).card := by
  classical
  let N (x : V) := (G.neighborFinset x).filter (fun u => G.edist v u = ((r+1 : ℕ) : ℕ∞))
  have hN (x : V) (hx : x ∈ sphere G v r) : (N x).card ≤ 2 := by
    have hx' : G.edist v x = (r : ℕ∞) := (Finset.mem_filter.mp hx).2
    have he : r-1+1 = r := by omega
    obtain ⟨w, hw, hdist⟩ := predecessor G v x (r-1) (by simpa [he] using hx')
    have hsub : N x ⊆ (G.neighborFinset x).erase w := by
      intro u hu
      obtain ⟨huN, hud⟩ := Finset.mem_filter.mp hu
      apply Finset.mem_erase.mpr
      refine ⟨?_, huN⟩
      intro heq
      subst u
      rw [hdist] at hud
      have : r-1 = r+1 := by exact_mod_cast hud
      omega
    have hmem : w ∈ G.neighborFinset x := by simpa using hw
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hmem] at hc
    have hdeg : (G.neighborFinset x).card = 3 := h3.degree_eq x
    omega
  have hsub : sphere G v (r+1) ⊆ (sphere G v r).biUnion N := by
    intro u hu
    have hud := (Finset.mem_filter.mp hu).2
    obtain ⟨w, hw, hdist⟩ := predecessor G v u r hud
    apply Finset.mem_biUnion.mpr
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨by simpa using hw.symm, hud⟩
  calc
    _ ≤ ((sphere G v r).biUnion N).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ sphere G v r, (N x).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ sphere G v r, 2 := Finset.sum_le_sum hN
    _ = _ := by simp [mul_comm]

private lemma sphere_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3)
    (v : V) (r : ℕ) : (sphere G v (r+1)).card ≤ 3 * 2^r := by
  classical
  induction r with
  | zero =>
    have he : sphere G v 1 = G.neighborFinset v := by
      ext u
      simp [sphere, G.edist_eq_one_iff_adj]
    simpa [he] using (h3.degree_eq v).le
  | succ r ih =>
    have hs := sphere_step G h3 v (r+1) (by omega)
    rw [pow_succ]
    nlinarith

private noncomputable def ball {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => G.edist v u ≤ (r : ℕ∞))

private lemma ball_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3)
    (v : V) (r : ℕ) : (ball G v r).card + 2 ≤ 3 * 2^r := by
  classical
  induction r with
  | zero =>
    have he : ball G v 0 = {v} := by ext u; simp [ball, G.edist_eq_zero_iff, eq_comm]
    simp [he]
  | succ r ih =>
    have hsub : ball G v (r+1) ⊆ ball G v r ∪ sphere G v (r+1) := by
      intro u hu
      have hh := (Finset.mem_filter.mp hu).2
      have hfinite : G.edist v u ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hh (ENat.natCast_lt_top _))
      lift G.edist v u to ℕ using hfinite with q hq
      have hle : q ≤ r+1 := by exact_mod_cast hh
      by_cases hqr : q ≤ r
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by rw [← hq]; exact_mod_cast hqr⟩
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by rw [← hq]; congr 1; omega⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hs := sphere_bound G h3 v r
    rw [pow_succ]
    omega

private lemma ball_half {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3)
    (hn : 8 ≤ Fintype.card V) (v : V) :
    2 * (ball G v (Nat.log 2 (Fintype.card V) - 3)).card ≤ Fintype.card V := by
  have hb := ball_bound G h3 v (Nat.log 2 (Fintype.card V) - 3)
  have hl : 3 ≤ Nat.log 2 (Fintype.card V) := by
    exact (Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hn))
  have he : 2^(Nat.log 2 (Fintype.card V)) =
      8 * 2^(Nat.log 2 (Fintype.card V)-3) := by
    calc
      _ = 2^((Nat.log 2 (Fintype.card V)-3)+3) := by rw [Nat.sub_add_cancel hl]
      _ = _ := by rw [pow_add]; ring
  have hp : 2^(Nat.log 2 (Fintype.card V)) ≤ Fintype.card V :=
    Nat.pow_log_le_self 2 (by omega)
  rw [he] at hp
  omega

private theorem half_pairs_far {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3)
    (hn : 8 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ^ 2 / 2 ≤
      ((Finset.univ.filter (fun p : V × V =>
        ((Nat.log 2 (Fintype.card V) - 2 : ℕ) : ℕ∞) ≤ G.edist p.1 p.2)).card : ℝ) := by
  classical
  let n := Fintype.card V
  let r := Nat.log 2 n - 3
  have hl : 3 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have he : Nat.log 2 n - 2 = r+1 := by dsimp [r]; omega
  let far (v : V) := Finset.univ.filter (fun u => ((r+1 : ℕ) : ℕ∞) ≤ G.edist v u)
  have hcount (v : V) : n ≤ 2 * (far v).card := by
    have hb := ball_half G h3 hn v
    have hc : (ball G v r).card + (far v).card = n := by
      have hcomp : far v = Finset.univ.filter (fun u => ¬ G.edist v u ≤ (r : ℕ∞)) := by
        ext u
        simp only [far, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
        exact ENat.natCast_add_one_le_iff
      rw [hcomp]
      exact Finset.card_filter_add_card_filter_not _
    dsimp [r, n] at *
    omega
  have htotal : (Finset.univ.filter (fun p : V × V =>
      ((r+1 : ℕ) : ℕ∞) ≤ G.edist p.1 p.2)).card = ∑ v : V, (far v).card := by
    simp only [Finset.card_filter, far, Fintype.sum_prod_type]
  have hs := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hcount v)
  have hs' : n*n ≤ 2 * (∑ v : V, (far v).card) := by simpa [← Finset.mul_sum] using hs
  rw [he, htotal]
  have hc : (n : ℝ)*(n : ℝ) ≤ 2 * ((∑ v : V, (far v).card : ℕ) : ℝ) := by exact_mod_cast hs'
  dsimp [n] at hc
  nlinarith

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
  have hfar : (n : ℝ)^2/2 ≤ (F.card : ℝ) := half_pairs_far G h3 hn
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



private theorem min_cut_ge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 < c) (hexp : IsEdgeExpander G c)
    (hn : 2 ≤ Fintype.card V) :
    c / ((Fintype.card V : ℝ) - 1) ≤ minCut (unitNetwork G) := by
  classical
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hV
  have hv : ({v} : Finset V)ᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hh := Finset.card_compl ({v} : Finset V)
    simp [he] at hh
    omega
  letI : Nonempty {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} :=
    ⟨⟨{v}, by simp, hv⟩⟩
  unfold minCut
  refine le_ciInf fun U => ?_
  have ha : 0 < U.val.card := U.property.1.card_pos
  have hb : 0 < U.valᶜ.card := U.property.2.card_pos
  have hs : U.val.card + U.valᶜ.card = Fintype.card V := by
    rw [Finset.card_compl]; exact Nat.add_sub_of_le (Finset.card_le_univ _)
  have hnR : 0 < (Fintype.card V : ℝ) - 1 := by
    have : (1 : ℝ) < Fintype.card V := by exact_mod_cast (show 1 < Fintype.card V by omega)
    linarith
  have haR : 0 < (U.val.card : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (U.valᶜ.card : ℝ) := by exact_mod_cast hb
  have hsR : (U.val.card : ℝ) + (U.valᶜ.card : ℝ) = Fintype.card V := by exact_mod_cast hs
  have he := hexp U.val
  unfold ratioCost
  rw [le_div_iff₀ (mul_pos haR hbR), div_mul_eq_mul_div, div_le_iff₀ hnR]
  push_cast at he
  rcases le_total U.val.card U.valᶜ.card with hab | hba
  · rw [min_eq_left (by exact_mod_cast hab : (U.val.card : ℝ) ≤ U.valᶜ.card)] at he
    have hbnd : (U.valᶜ.card : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
      have : (1 : ℝ) ≤ U.val.card := by exact_mod_cast ha
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hbnd (mul_nonneg hc.le haR.le),
      mul_le_mul_of_nonneg_right he hnR.le]
  · rw [min_eq_right (by exact_mod_cast hba : (U.valᶜ.card : ℝ) ≤ U.val.card)] at he
    have hbnd : (U.val.card : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
      have : (1 : ℝ) ≤ U.valᶜ.card := by exact_mod_cast hb
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hbnd (mul_nonneg hc.le hbR.le),
      mul_le_mul_of_nonneg_right he hnR.le]



theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3)
    (c : ℝ) (hc : 0 < c) (hexp : IsEdgeExpander G c)
    (hn : 8 ≤ Fintype.card V) :
    maxFlow (unitNetwork G) uniformDemand ≤
      6 * minCut (unitNetwork G) /
        (c * ((Nat.log 2 (Fintype.card V) : ℝ) - 2)) := by
  have hflow := max_flow_le G h3 hn
  have hcut := min_cut_ge G c hc hexp (by omega)
  have hnR : (8 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlog : 3 ≤ Nat.log 2 (Fintype.card V) := Nat.le_log_of_pow_le (by norm_num) hn
  have hlogR : (3 : ℝ) ≤ Nat.log 2 (Fintype.card V) := by exact_mod_cast hlog
  have hnpos : 0 < (Fintype.card V : ℝ)-1 := by linarith
  have hrpos : 0 < (Nat.log 2 (Fintype.card V) : ℝ)-2 := by linarith
  apply hflow.trans
  rw [div_le_div_iff₀ (mul_pos hnpos hrpos) (mul_pos hc hrpos)]
  have hcut' := (div_le_iff₀ hnpos).mp hcut
  nlinarith [mul_le_mul_of_nonneg_right hcut' hrpos.le]

#print axioms solution
