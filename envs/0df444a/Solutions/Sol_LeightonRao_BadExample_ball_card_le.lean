-- Prove2me | solution 1 for LeightonRao.BadExample.ball_card_le
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:17:59.750987+00:00
-- url     : https://prove2.me/submissions/b8b67273-ee44-4699-a567-ee819ad50a62

import Mathlib
import Definitions.Def_LeightonRao_BadExample_Setting
set_option autoImplicit false
open scoped BigOperators

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

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3)
    (hn : 8 ≤ Fintype.card V) (v : V) :
    2 * ((Finset.univ.filter (fun u =>
        G.edist v u ≤ ((Nat.log 2 (Fintype.card V) - 3 : ℕ) : ℕ∞))).card : ℝ)
      ≤ (Fintype.card V : ℝ) := by
  have hh := ball_half G h3 hn v
  exact_mod_cast hh

#print axioms solution
