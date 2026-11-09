-- Prove2me | solution 1 for LeightonRao.ShortPaths.short_path_duality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:47:25.86174+00:00
-- url     : https://prove2.me/submissions/83a8b814-1ada-400d-af97-2d5b90a76ecf

import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace LeightonRao.ShortPaths

open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

instance {α β : Type*} [Fintype α] [DecidableEq β] : DecidableEq (α → β) :=
  Fintype.decidablePiFintype

/-! ### Part 1: Weak Duality and Basic Properties -/

private lemma distL_self_zero (N : Network V) (d : V → V → ℝ) {B : ℝ} (hB : 0 ≤ B) (u : V) :
    distL N d B u u = 0 := by
  rw [← nonpos_iff_eq_zero]
  unfold distL
  have hnil : ((SimpleGraph.Walk.nil : N.graph.Walk u u).length : ℝ) ≤ B := by simp [hB]
  refine (iInf₂_le SimpleGraph.Walk.nil hnil).trans ?_
  simp [walkLen]

private lemma distL_anti_bound (N : Network V) (d : V → V → ℝ) {B₁ B₂ : ℝ} (hB : B₁ ≤ B₂) (u v : V) :
    distL N d B₂ u v ≤ distL N d B₁ u v := by
  unfold distL
  refine le_iInf₂ fun p hp => ?_
  exact iInf₂_le p (hp.trans hB)

private lemma distL_step_of_pos_cap (N : Network V) {d : V → V → ℝ}
    (hd : IsDistanceFunction d) {i j : V} (hC : 0 < N.C i j) (h : ℕ) (s : V) :
    distL N d ((h + 1 : ℕ) : ℝ) s j ≤ distL N d (h : ℝ) s i + ENNReal.ofReal (d i j) := by
  have hij : i ≠ j := by
    intro heq
    subst heq
    linarith [N.C_self i]
  have hadj : N.graph.Adj i j := by
    simp [Network.graph, SimpleGraph.fromRel_adj, hij, hC]
  have hstep : ∀ (p : N.graph.Walk s i), (p.length : ℝ) ≤ (h : ℝ) →
      distL N d ((h + 1 : ℕ) : ℝ) s j ≤ ENNReal.ofReal (walkLen d p) + ENNReal.ofReal (d i j) := by
    intro p hp
    let q : N.graph.Walk i j := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
    let pq : N.graph.Walk s j := p.append q
    have hpq_len : (pq.length : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by
      have : pq.length = p.length + 1 := by simp [pq, q, SimpleGraph.Walk.length_append]
      rw [this]
      push_cast
      linarith
    have hpq_wt : walkLen d pq = walkLen d p + d i j := by
      unfold walkLen
      simp [pq, q, SimpleGraph.Walk.darts_append]
    have hp_nn : 0 ≤ walkLen d p := by
      unfold walkLen
      apply List.sum_nonneg
      intro x hx
      rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
      exact hd.1 a.fst a.snd
    refine (iInf₂_le pq hpq_len).trans ?_
    rw [hpq_wt, ENNReal.ofReal_add hp_nn (hd.1 i j)]
  unfold distL
  rw [ENNReal.iInf_add]
  refine le_iInf fun p => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hp => hstep p hp

private lemma zero_isShortConcurrentFlow (N : Network V) (L : ℕ) :
    IsShortConcurrentFlow N uniformDemand L (fun _ _ _ _ _ => 0) 0 := by
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t _ v; simp
  · intro s t h _ _ v; simp
  · intro s t h _ _; simp
  · intro s t h _ _ v _; simp
  · intro s t _; simp
  · intro i j
    simp only [add_zero, Finset.sum_const_zero]
    exact N.C_nonneg i j

private lemma feasible_set_nonempty (N : Network V) (L : ℕ) :
    {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsShortConcurrentFlow N uniformDemand L f lam}.Nonempty :=
  ⟨0, le_rfl, ⟨_, zero_isShortConcurrentFlow N L⟩⟩

private lemma totalWeight_nonneg (N : Network V) {d : V → V → ℝ} (hd : IsDistanceFunction d) :
    0 ≤ totalWeight N d := by
  unfold totalWeight
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => ?_)
  exact mul_nonneg (N.C_nonneg u v) (hd.1 u v)

private lemma flow_le_cap_of_isShortConcurrentFlow {N : Network V} {L : ℕ}
    {f : V → V → ℕ → V → V → ℝ} {lam : ℝ}
    (hf : IsShortConcurrentFlow N uniformDemand L f lam)
    (s t : V) {h : ℕ} (hh : h < L) (i j : V) :
    f s t h i j ≤ N.C i j := by
  have h1 := hf.1
  have h9 := hf.2.2.2.2.2.2.2.2 i j
  have hle1 : f s t h i j ≤ f s t h i j + f s t h j i := le_add_of_nonneg_right (h1 s t h j i)
  have hle2 : f s t h i j + f s t h j i ≤
      ∑ h' ∈ Finset.range L, (f s t h' i j + f s t h' j i) := by
    refine Finset.single_le_sum (f := fun h' => f s t h' i j + f s t h' j i)
      (fun h' _ => add_nonneg (h1 s t h' i j) (h1 s t h' j i))
      (Finset.mem_range.mpr hh)
  have hle3 : ∑ h' ∈ Finset.range L, (f s t h' i j + f s t h' j i) ≤
      ∑ t' : V, ∑ h' ∈ Finset.range L, (f s t' h' i j + f s t' h' j i) := by
    refine Finset.single_le_sum (f := fun t' => ∑ h' ∈ Finset.range L, (f s t' h' i j + f s t' h' j i))
      (fun t' _ => Finset.sum_nonneg fun h' _ => add_nonneg (h1 s t' h' i j) (h1 s t' h' j i))
      (Finset.mem_univ t)
  have hle4 : ∑ t' : V, ∑ h' ∈ Finset.range L, (f s t' h' i j + f s t' h' j i) ≤
      ∑ s' : V, ∑ t' : V, ∑ h' ∈ Finset.range L, (f s' t' h' i j + f s' t' h' j i) := by
    refine Finset.single_le_sum (f := fun s' => ∑ t' : V, ∑ h' ∈ Finset.range L, (f s' t' h' i j + f s' t' h' j i))
      (fun s' _ => Finset.sum_nonneg fun t' _ => Finset.sum_nonneg fun h' _ =>
        add_nonneg (h1 s' t' h' i j) (h1 s' t' h' j i))
      (Finset.mem_univ s)
  linarith

private lemma commodity_cost_bound (N : Network V) {d : V → V → ℝ}
    (hd : IsDistanceFunction d) {L : ℕ} (hL : 0 < L)
    {f : V → V → ℕ → V → V → ℝ} {lam : ℝ}
    (hf : IsShortConcurrentFlow N uniformDemand L f lam)
    (s t : V) :
    ENNReal.ofReal (lam * uniformDemand s t) * distL N d (L : ℝ) s t ≤
      ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, ENNReal.ofReal (f s t h i j * d i j) := by
  by_cases hst : s = t
  · simp [hst, uniformDemand]
  · let A : ℕ → ENNReal := fun k =>
      if k < L then
        ∑ i : V, ENNReal.ofReal (∑ j : V, f s t k i j) * distL N d (k : ℝ) s i
      else 0
    have hA0 : A 0 = 0 := by
      dsimp [A]
      rw [if_pos hL]
      apply Finset.sum_eq_zero
      intro i _
      by_cases his : i = s
      · subst his
        rw [Nat.cast_zero, distL_self_zero N d le_rfl i, mul_zero]
      · have h0 := hf.2.2.2.1 s t hst i
        rw [if_neg his] at h0
        rw [h0, ENNReal.ofReal_zero, zero_mul]
    have hstep : ∀ k : ℕ, k < L →
        A (k + 1) + ENNReal.ofReal (∑ i : V, f s t k i t) * distL N d (L : ℝ) s t ≤
          A k + ∑ i : V, ∑ j : V, ENNReal.ofReal (f s t k i j * d i j) := by
      intro k hk
      have hedge : ∀ i j : V,
          ENNReal.ofReal (f s t k i j) * distL N d ((k + 1 : ℕ) : ℝ) s j ≤
            ENNReal.ofReal (f s t k i j) * distL N d (k : ℝ) s i +
              ENNReal.ofReal (f s t k i j * d i j) := by
        intro i j
        have hf_nn := hf.1 s t k i j
        rcases eq_or_lt_of_le hf_nn with hzero | hpos
        · rw [← hzero]
          simp
        · have hC : 0 < N.C i j := lt_of_lt_of_le hpos (flow_le_cap_of_isShortConcurrentFlow hf s t hk i j)
          have hdist := distL_step_of_pos_cap N hd hC k s
          calc
            ENNReal.ofReal (f s t k i j) * distL N d ((k + 1 : ℕ) : ℝ) s j
              ≤ ENNReal.ofReal (f s t k i j) * (distL N d (k : ℝ) s i + ENNReal.ofReal (d i j)) := by
                gcongr
            _ = ENNReal.ofReal (f s t k i j) * distL N d (k : ℝ) s i +
                  ENNReal.ofReal (f s t k i j * d i j) := by
                rw [mul_add, ← ENNReal.ofReal_mul hf_nn]
      have hsum_ij :
          ∑ j : V, ENNReal.ofReal (∑ i : V, f s t k i j) * distL N d ((k + 1 : ℕ) : ℝ) s j ≤
            A k + ∑ i : V, ∑ j : V, ENNReal.ofReal (f s t k i j * d i j) := by
        have h_lhs : ∑ j : V, ENNReal.ofReal (∑ i : V, f s t k i j) * distL N d ((k + 1 : ℕ) : ℝ) s j =
            ∑ i : V, ∑ j : V, ENNReal.ofReal (f s t k i j) * distL N d ((k + 1 : ℕ) : ℝ) s j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hf.1 s t k i j), Finset.sum_mul]
        have h_rhs : A k = ∑ i : V, ∑ j : V, ENNReal.ofReal (f s t k i j) * distL N d (k : ℝ) s i := by
          dsimp [A]
          rw [if_pos hk]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hf.1 s t k i j), Finset.sum_mul]
        rw [h_lhs, h_rhs, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun j _ => hedge i j
      refine le_trans ?_ hsum_ij
      have hsplit := (Finset.sum_erase_add Finset.univ
        (fun j : V => ENNReal.ofReal (∑ i : V, f s t k i j) * distL N d ((k + 1 : ℕ) : ℝ) s j)
        (Finset.mem_univ t)).symm
      rw [hsplit]
      refine add_le_add ?_ ?_
      · dsimp [A]
        split_ifs with hk1
        · have h_t_zero : ENNReal.ofReal (∑ j : V, f s t (k + 1) t j) * distL N d ((k + 1 : ℕ) : ℝ) s t = 0 := by
            rw [hf.2.2.2.2.2.1 s t (k + 1) hst hk1, ENNReal.ofReal_zero, zero_mul]
          rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ t), h_t_zero, add_zero]
          refine le_of_eq (Finset.sum_congr rfl fun v hv => ?_)
          have hvt : v ≠ t := Finset.ne_of_mem_erase hv
          have h5 := hf.2.2.2.2.1 s t k hst hk1 v
          rw [if_neg hvt] at h5
          rw [h5]
        · simp
      · have hle_nat : (k + 1 : ℕ) ≤ L := by omega
        have hdist_le : distL N d (L : ℝ) s t ≤ distL N d ((k + 1 : ℕ) : ℝ) s t :=
          distL_anti_bound N d (Nat.cast_le.mpr hle_nat) s t
        gcongr
    have hind : ∀ m : ℕ, m ≤ L →
        A m + (∑ h ∈ Finset.range m, ENNReal.ofReal (∑ i : V, f s t h i t)) * distL N d (L : ℝ) s t ≤
          ∑ h ∈ Finset.range m, ∑ i : V, ∑ j : V, ENNReal.ofReal (f s t h i j * d i j) := by
      intro m hm
      induction m with
      | zero => simp [hA0]
      | succ m ih =>
        have hmL : m < L := by omega
        have ih' := ih (by omega)
        have hst_m := hstep m hmL
        rw [Finset.sum_range_succ, Finset.sum_range_succ, add_mul]
        calc
          A (m + 1) +
              ((∑ x ∈ Finset.range m, ENNReal.ofReal (∑ i : V, f s t x i t)) * distL N d (L : ℝ) s t +
                ENNReal.ofReal (∑ i : V, f s t m i t) * distL N d (L : ℝ) s t)
            = (A (m + 1) + ENNReal.ofReal (∑ i : V, f s t m i t) * distL N d (L : ℝ) s t) +
                (∑ x ∈ Finset.range m, ENNReal.ofReal (∑ i : V, f s t x i t)) * distL N d (L : ℝ) s t := by
              ac_rfl
          _ ≤ (A m + ∑ i : V, ∑ j : V, ENNReal.ofReal (f s t m i j * d i j)) +
                (∑ x ∈ Finset.range m, ENNReal.ofReal (∑ i : V, f s t x i t)) * distL N d (L : ℝ) s t := by
              gcongr
          _ = (A m + (∑ x ∈ Finset.range m, ENNReal.ofReal (∑ i : V, f s t x i t)) * distL N d (L : ℝ) s t) +
                ∑ i : V, ∑ j : V, ENNReal.ofReal (f s t m i j * d i j) := by
              ac_rfl
          _ ≤ (∑ h ∈ Finset.range m, ∑ i : V, ∑ j : V, ENNReal.ofReal (f s t h i j * d i j)) +
                ∑ i : V, ∑ j : V, ENNReal.ofReal (f s t m i j * d i j) := by
              gcongr
    have hL_res := hind L le_rfl
    have hAL : A L = 0 := by dsimp [A]; rw [if_neg (lt_irrefl L)]
    rw [hAL, zero_add] at hL_res
    have hsum_t : ∑ h ∈ Finset.range L, ENNReal.ofReal (∑ i : V, f s t h i t) =
        ENNReal.ofReal (lam * uniformDemand s t) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun h _ => Finset.sum_nonneg fun i _ => hf.1 s t h i t)]
      rw [hf.2.2.2.2.2.2.2.1 s t hst]
    rwa [hsum_t] at hL_res

private lemma flow_val_le_totalWeight (N : Network V) (hn : 2 ≤ Fintype.card V)
    {d : V → V → ℝ} (hd : IsDistanceFunction d) {L : ℕ}
    (hshort : SatisfiesShortConstraint N d L)
    {f : V → V → ℕ → V → V → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hf : IsShortConcurrentFlow N uniformDemand L f lam) :
    lam ≤ totalWeight N d := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have hcard : 1 < Fintype.card V := by omega
    obtain ⟨s, t, hst⟩ := Fintype.exists_pair_of_one_lt_card hcard
    have h8 := hf.2.2.2.2.2.2.2.1 s t hst
    simp [uniformDemand, hst] at h8
    have hlam0 : lam = 0 := by linarith
    rw [hlam0]
    exact totalWeight_nonneg N hd
  · have hsum_st :
        ENNReal.ofReal lam * ((1 / 2 : ENNReal) * ∑ s : V, ∑ t : V, distL N d (L : ℝ) s t) ≤
          ENNReal.ofReal (totalWeight N d) := by
      have h_lhs :
          ENNReal.ofReal lam * ((1 / 2 : ENNReal) * ∑ s : V, ∑ t : V, distL N d (L : ℝ) s t) =
            ∑ s : V, ∑ t : V, ENNReal.ofReal (lam * uniformDemand s t) * distL N d (L : ℝ) s t := by
        rw [← mul_assoc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hst : s = t
        · subst hst
          rw [distL_self_zero N d (by positivity) s, mul_zero, mul_zero]
        · have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
          rw [hhalf, ← ENNReal.ofReal_mul hlam]
          simp [uniformDemand, hst]
      rw [h_lhs]
      have h_ofReal_5 :
          (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V,
            ENNReal.ofReal (f s t h i j * d i j)) =
          ENNReal.ofReal (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V,
            f s t h i j * d i j) := by
        have hnn : ∀ s t h i j, 0 ≤ f s t h i j * d i j :=
          fun s t h i j => mul_nonneg (hf.1 s t h i j) (hd.1 i j)
        rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => Finset.sum_nonneg fun t _ =>
          Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn s t h i j)]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => Finset.sum_nonneg fun h _ =>
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn s t h i j)]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun h _ => Finset.sum_nonneg fun i _ =>
          Finset.sum_nonneg fun j _ => hnn s t h i j)]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hnn s t h i j)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hnn s t h i j)]
      calc
        ∑ s : V, ∑ t : V, ENNReal.ofReal (lam * uniformDemand s t) * distL N d (L : ℝ) s t
          ≤ ∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V,
              ENNReal.ofReal (f s t h i j * d i j) :=
            Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ =>
              commodity_cost_bound N hd hL hf s t
        _ = ENNReal.ofReal (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V,
              f s t h i j * d i j) := h_ofReal_5
        _ ≤ ENNReal.ofReal (totalWeight N d) := by
            apply ENNReal.ofReal_le_ofReal
            have hpull :
                ∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, f s t h i j * d i j =
                  ∑ i : V, ∑ j : V, (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, f s t h i j) * d i j := by
              have h1 : ∀ s t, ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, f s t h i j * d i j =
                  ∑ i : V, ∑ j : V, ∑ h ∈ Finset.range L, f s t h i j * d i j := by
                intro s t
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
              have h2 : ∀ s, ∑ t : V, ∑ i : V, ∑ j : V, ∑ h ∈ Finset.range L, f s t h i j * d i j =
                  ∑ i : V, ∑ j : V, ∑ t : V, ∑ h ∈ Finset.range L, f s t h i j * d i j := by
                intro s
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
              have h3 : ∑ s : V, ∑ i : V, ∑ j : V, ∑ t : V, ∑ h ∈ Finset.range L, f s t h i j * d i j =
                  ∑ i : V, ∑ j : V, ∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, f s t h i j * d i j := by
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
              simp_rw [h1, h2, h3, Finset.sum_mul]
            have hsymm :
                ∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, f s t h i j * d i j =
                  (1 / 2 : ℝ) * ∑ i : V, ∑ j : V,
                    (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, (f s t h i j + f s t h j i)) * d i j := by
              have hswap :
                  ∑ i : V, ∑ j : V, (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, f s t h j i) * d i j =
                    ∑ i : V, ∑ j : V, (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, f s t h i j) * d i j := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                rw [hd.2 j i]
              have hrhs : ∑ i : V, ∑ j : V,
                    (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, (f s t h i j + f s t h j i)) * d i j =
                  (∑ i : V, ∑ j : V, (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, f s t h i j) * d i j) +
                  (∑ i : V, ∑ j : V, (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, f s t h j i) * d i j) := by
                simp only [Finset.sum_add_distrib, add_mul]
              rw [hpull, hrhs, hswap]
              ring
            rw [hsymm]
            unfold totalWeight
            gcongr with i _ j _
            · exact hd.1 i j
            · exact hf.2.2.2.2.2.2.2.2 i j
    have h1 : ENNReal.ofReal lam ≤ ENNReal.ofReal (totalWeight N d) := by
      calc
        ENNReal.ofReal lam = ENNReal.ofReal lam * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal lam * ((1 / 2 : ENNReal) * ∑ s : V, ∑ t : V, distL N d (L : ℝ) s t) := by
          gcongr
          exact hshort
        _ ≤ ENNReal.ofReal (totalWeight N d) := hsum_st
    exact (ENNReal.ofReal_le_ofReal_iff (totalWeight_nonneg N hd)).mp h1

private lemma weak_duality (N : Network V) (hn : 2 ≤ Fintype.card V) (L : ℕ)
    (d : V → V → ℝ) (hd : IsDistanceFunction d) (hshort : SatisfiesShortConstraint N d L) :
    maxShortFlow N uniformDemand L ≤ totalWeight N d := by
  unfold maxShortFlow
  refine csSup_le (feasible_set_nonempty N L) ?_
  rintro lam ⟨hlam, f, hf⟩
  exact flow_val_le_totalWeight N hn hd hshort hlam hf

/-! ### Part 2: Primal Attainment via Compactness -/

private abbrev FlowFin (V : Type) (L : ℕ) := V → V → Fin L → V → V → ℝ

private def extFlow {L : ℕ} (g : FlowFin V L) (s t : V) (h : ℕ) (i j : V) : ℝ :=
  if hh : h < L then g s t ⟨h, hh⟩ i j else 0

private def resFlow {L : ℕ} (f : V → V → ℕ → V → V → ℝ) : FlowFin V L :=
  fun s t h i j => f s t h.1 i j

private lemma extFlow_resFlow {L : ℕ} {f : V → V → ℕ → V → V → ℝ}
    (h_vanish : ∀ s t h i j, L ≤ h → f s t h i j = 0) :
    extFlow (resFlow (L := L) f) = f := by
  ext s t h i j
  unfold extFlow resFlow
  split_ifs with hh
  · rfl
  · exact (h_vanish s t h i j (by omega)).symm

private lemma lam_le_bound_of_isShortConcurrentFlow (N : Network V) (hn : 2 ≤ Fintype.card V)
    {L : ℕ} {f : V → V → ℕ → V → V → ℝ} {lam : ℝ}
    (hf : IsShortConcurrentFlow N uniformDemand L f lam) :
    lam ≤ 2 * ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, N.C i j := by
  have hcard : 1 < Fintype.card V := by omega
  obtain ⟨s, t, hst⟩ := Fintype.exists_pair_of_one_lt_card hcard
  have h8 := hf.2.2.2.2.2.2.2.1 s t hst
  have hdem : uniformDemand s t = 1 / 2 := if_neg hst
  rw [hdem] at h8
  have hsum_le : ∑ h ∈ Finset.range L, ∑ i : V, f s t h i t ≤
      ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, N.C i j := by
    refine Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun i _ => ?_
    have hh' : h < L := Finset.mem_range.mp hh
    have h1 : f s t h i t ≤ N.C i t := flow_le_cap_of_isShortConcurrentFlow hf s t hh' i t
    have h2 : N.C i t ≤ ∑ j : V, N.C i j := by
      refine Finset.single_le_sum (f := fun j : V => N.C i j) (fun j _ => N.C_nonneg i j) (Finset.mem_univ t)
    linarith
  linarith

private lemma isClosed_isShortConcurrentFlow_ext (N : Network V) (L : ℕ) :
    IsClosed {p : ℝ × FlowFin V L | 0 ≤ p.1 ∧ IsShortConcurrentFlow N uniformDemand L (extFlow p.2) p.1} := by
  have h_eq : {p : ℝ × FlowFin V L | 0 ≤ p.1 ∧ IsShortConcurrentFlow N uniformDemand L (extFlow p.2) p.1} =
      {p : ℝ × FlowFin V L | 0 ≤ p.1} ∩
      (⋂ (s : V) (t : V) (h : Fin L) (i : V) (j : V), {p : ℝ × FlowFin V L | 0 ≤ p.2 s t h i j}) ∩
      (⋂ (s : V) (h : Fin L) (i : V) (j : V), {p : ℝ × FlowFin V L | p.2 s s h i j = 0}) ∩
      (⋂ (s : V) (t : V) (_ : s ≠ t) (v : V),
        {p : ℝ × FlowFin V L | (∑ j : V, extFlow p.2 s t 0 v j) = if v = s then p.1 * uniformDemand s t else 0}) ∩
      (⋂ (s : V) (t : V) (h : Fin L) (_ : s ≠ t) (_ : h.1 + 1 < L) (v : V),
        {p : ℝ × FlowFin V L | (∑ j : V, extFlow p.2 s t (h.1 + 1) v j) =
          if v = t then 0 else ∑ i : V, p.2 s t h i v}) ∩
      (⋂ (s : V) (t : V) (h : Fin L) (_ : s ≠ t),
        {p : ℝ × FlowFin V L | (∑ j : V, p.2 s t h t j) = 0}) ∩
      (⋂ (s : V) (t : V) (h : Fin L) (_ : s ≠ t) (_ : h.1 + 1 = L) (v : V) (_ : v ≠ t),
        {p : ℝ × FlowFin V L | (∑ i : V, p.2 s t h i v) = 0}) ∩
      (⋂ (s : V) (t : V) (_ : s ≠ t),
        {p : ℝ × FlowFin V L | (∑ h : Fin L, ∑ i : V, p.2 s t h i t) = p.1 * uniformDemand s t}) ∩
      (⋂ (i : V) (j : V),
        {p : ℝ × FlowFin V L | (∑ s : V, ∑ t : V, ∑ h : Fin L, (p.2 s t h i j + p.2 s t h j i)) ≤ N.C i j}) := by
    ext ⟨lam, g⟩
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hlam, h1, _, h3, h4, h5, h6, h7, h8, h9⟩
      refine ⟨⟨⟨⟨⟨⟨⟨⟨hlam, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · intro s t h i j; simpa [extFlow, h.2] using h1 s t h.1 i j
      · intro s h i j; simpa [extFlow, h.2] using h3 s h.1 i j
      · intro s t hst v; exact h4 s t hst v
      · intro s t h hst hh v
        have := h5 s t h.1 hst hh v
        simpa [extFlow, h.2] using this
      · intro s t h hst; simpa [extFlow, h.2] using h6 s t h.1 hst h.2
      · intro s t h hst hh v hvt; simpa [extFlow, h.2] using h7 s t h.1 hst hh v hvt
      · intro s t hst
        rw [← h8 s t hst, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun h _ => ?_
        simp [extFlow, h.2]
      · intro i j
        have := h9 i j
        have hconv : (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, (extFlow g s t h i j + extFlow g s t h j i)) =
            ∑ s : V, ∑ t : V, ∑ h : Fin L, (g s t h i j + g s t h j i) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
          rw [← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl fun h _ => ?_
          simp [extFlow, h.2]
        rwa [← hconv]
    · rintro ⟨⟨⟨⟨⟨⟨⟨⟨hlam, h1⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
      refine ⟨hlam, ?_, ?_, ?_, h4, ?_, ?_, ?_, ?_, ?_⟩
      · intro s t h i j
        unfold extFlow
        split_ifs with hh
        · exact h1 s t ⟨h, hh⟩ i j
        · exact le_rfl
      · intro s t h i j hh
        unfold extFlow
        exact dif_neg (by omega)
      · intro s h i j
        unfold extFlow
        split_ifs with hh
        · exact h3 s ⟨h, hh⟩ i j
        · rfl
      · intro s t h hst hh v
        have hhL : h < L := by omega
        have := h5 s t ⟨h, hhL⟩ hst hh v
        simpa [extFlow, hhL] using this
      · intro s t h hst hh
        simpa [extFlow, hh] using h6 s t ⟨h, hh⟩ hst
      · intro s t h hst hh v hvt
        have hhL : h < L := by omega
        simpa [extFlow, hhL] using h7 s t ⟨h, hhL⟩ hst hh v hvt
      · intro s t hst
        rw [← Fin.sum_univ_eq_sum_range]
        simpa [extFlow] using h8 s t hst
      · intro i j
        have hconv : (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L, (extFlow g s t h i j + extFlow g s t h j i)) =
            ∑ s : V, ∑ t : V, ∑ h : Fin L, (g s t h i j + g s t h j i) := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
          rw [← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl fun h _ => ?_
          simp [extFlow, h.2]
        rw [hconv]
        exact h9 i j
  have hcont_ext : ∀ s t h v j, Continuous (fun p : ℝ × FlowFin V L => extFlow p.2 s t h v j) := by
    intro s t h v j
    unfold extFlow
    split_ifs with hh
    · fun_prop
    · exact continuous_const
  rw [h_eq]
  refine ((((((((isClosed_le continuous_const continuous_fst).inter ?_).inter ?_).inter ?_).inter ?_).inter ?_).inter ?_).inter ?_).inter ?_
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun h =>
      isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop)
  · exact isClosed_iInter fun s => isClosed_iInter fun h => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_iInter fun v => isClosed_eq
        (continuous_finsetSum _ fun j _ => hcont_ext s t 0 v j)
        (by split_ifs <;> fun_prop)
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun h =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun v =>
        isClosed_eq (continuous_finsetSum _ fun j _ => hcont_ext s t (h.1 + 1) v j)
          (by split_ifs <;> fun_prop)
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun h =>
      isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun h =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun v =>
        isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (by fun_prop) continuous_const

private lemma primal_attainment (N : Network V) (hn : 2 ≤ Fintype.card V) (L : ℕ) :
    (∃ f : V → V → ℕ → V → V → ℝ,
      IsShortConcurrentFlow N uniformDemand L f (maxShortFlow N uniformDemand L)) ∧
    0 ≤ maxShortFlow N uniformDemand L ∧
    BddAbove {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsShortConcurrentFlow N uniformDemand L f lam} := by
  let M : ℝ := 2 * ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, N.C i j
  have hM_nn : 0 ≤ M := by
    dsimp [M]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => N.C_nonneg i j)
  let B : Set (ℝ × FlowFin V L) :=
    Set.Icc 0 M ×ˢ
      {g : FlowFin V L | ∀ s t h i j, g s t h i j ∈ Set.Icc 0 (N.C i j)}
  have hB_compact : IsCompact B := by
    refine isCompact_Icc.prod ?_
    have h_pi : {g : FlowFin V L | ∀ s t h i j, g s t h i j ∈ Set.Icc 0 (N.C i j)} =
        Set.pi Set.univ fun s => Set.pi Set.univ fun t => Set.pi Set.univ fun h =>
          Set.pi Set.univ fun i => Set.pi Set.univ fun j => Set.Icc 0 (N.C i j) := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
    rw [h_pi]
    exact isCompact_univ_pi fun s => isCompact_univ_pi fun t => isCompact_univ_pi fun h =>
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc
  let F : Set (ℝ × FlowFin V L) :=
    {p : ℝ × FlowFin V L | 0 ≤ p.1 ∧ IsShortConcurrentFlow N uniformDemand L (extFlow p.2) p.1}
  have hF_sub_B : F ⊆ B := by
    rintro ⟨lam, g⟩ ⟨hlam, hf⟩
    refine ⟨⟨hlam, lam_le_bound_of_isShortConcurrentFlow N hn hf⟩, fun s t h i j => ⟨?_, ?_⟩⟩
    · simpa [extFlow, h.2] using hf.1 s t h.1 i j
    · simpa [extFlow, h.2] using flow_le_cap_of_isShortConcurrentFlow hf s t h.2 i j
  have hF_compact : IsCompact F :=
    hB_compact.of_isClosed_subset (isClosed_isShortConcurrentFlow_ext N L) hF_sub_B
  have h0_mem : ((0 : ℝ), (fun _ _ _ _ _ => 0 : FlowFin V L)) ∈ F := by
    refine ⟨le_rfl, ?_⟩
    have h_ext0 : extFlow (fun _ _ _ _ _ => 0 : FlowFin V L) = fun _ _ _ _ _ => 0 := by
      ext s t h i j; simp [extFlow]
    rw [h_ext0]
    exact zero_isShortConcurrentFlow N L
  obtain ⟨⟨lam_star, g_star⟩, h_mem, h_max⟩ :=
    hF_compact.exists_isMaxOn ⟨_, h0_mem⟩ continuous_fst.continuousOn
  have hS_eq : {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsShortConcurrentFlow N uniformDemand L f lam} =
      Prod.fst '' F := by
    ext lam
    simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, F]
    constructor
    · rintro ⟨hlam, f, hf⟩
      refine ⟨lam, resFlow f, ⟨hlam, ?_⟩, rfl⟩
      rwa [extFlow_resFlow hf.2.1]
    · rintro ⟨lam', g, ⟨hlam', hf⟩, rfl⟩
      exact ⟨hlam', extFlow g, hf⟩
  have hbdd : BddAbove {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsShortConcurrentFlow N uniformDemand L f lam} := by
    refine ⟨lam_star, ?_⟩
    rw [hS_eq]
    rintro _ ⟨p, hp, rfl⟩
    exact h_max hp
  have h_sup_eq : maxShortFlow N uniformDemand L = lam_star := by
    unfold maxShortFlow
    apply le_antisymm
    · refine csSup_le (feasible_set_nonempty N L) ?_
      rw [hS_eq]
      rintro _ ⟨p, hp, rfl⟩
      exact h_max hp
    · refine le_csSup hbdd ?_
      rw [hS_eq]
      exact ⟨(lam_star, g_star), h_mem, rfl⟩
  rw [h_sup_eq]
  exact ⟨⟨extFlow g_star, h_mem.2⟩, h_mem.1, hbdd⟩

/-! ### Part 3: Strong Duality via Farkas' Lemma on the Walk LP -/

private lemma farkas_inequality_form_fintype₂
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (b : ι → ℝ) (c : κ → ℝ) (d : ℝ)
    (hfeas : ∃ x : κ → ℝ, A.mulVec x ≤ b) :
    (∀ x : κ → ℝ, A.mulVec x ≤ b → c ⬝ᵥ x ≤ d) →
      ∃ p : ι → ℝ, 0 ≤ p ∧ Aᵀ.mulVec p = c ∧ p ⬝ᵥ b ≤ d := by
  classical
  intro hub
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let A' : Matrix ι (Fin (Fintype.card κ)) ℝ := fun r j => A r (e.symm j)
  let c' : Fin (Fintype.card κ) → ℝ := fun j => c (e.symm j)
  have hfeas' : ∃ x' : Fin (Fintype.card κ) → ℝ, A'.mulVec x' ≤ b := by
    rcases hfeas with ⟨x, hx⟩
    refine ⟨fun j => x (e.symm j), fun r => ?_⟩
    have hmul : A'.mulVec (fun j => x (e.symm j)) r = A.mulVec x r := by
      unfold Matrix.mulVec dotProduct A'
      exact e.symm.sum_comp (fun k => A r k * x k)
    rw [hmul]
    exact hx r
  have hub' : ∀ x' : Fin (Fintype.card κ) → ℝ, A'.mulVec x' ≤ b → c' ⬝ᵥ x' ≤ d := by
    intro x' hx'
    let x : κ → ℝ := fun k => x' (e k)
    have hmul : A.mulVec x = A'.mulVec x' := by
      ext r
      unfold Matrix.mulVec dotProduct A' x
      exact (e.symm.sum_comp (fun k => A r k * x' (e k))).symm.trans
        (Finset.sum_congr rfl fun j _ => by simp)
    have hdot : c' ⬝ᵥ x' = c ⬝ᵥ x := by
      unfold dotProduct c' x
      exact (Finset.sum_congr rfl fun j _ => by simp).trans
        (e.symm.sum_comp (fun k => c k * x' (e k)))
    rw [hdot]
    exact hub x (by rwa [hmul])
  obtain ⟨p, hp_nn, hp_eq, hp_ub⟩ :=
    (LinearOptimization.farkas_inequality_form_fintype A' b c' d hfeas').mp hub'
  refine ⟨p, hp_nn, ?_, hp_ub⟩
  ext k
  have hk := congrFun hp_eq (e k)
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at hk ⊢
  simpa only [A', c', Equiv.symm_apply_apply] using hk

private lemma farkas_standard_form
    {ι_eq ι_ineq κ : Type*} [Fintype ι_eq] [Fintype ι_ineq] [Fintype κ]
    (E : Matrix ι_eq κ ℝ) (I : Matrix ι_ineq κ ℝ) (b : ι_ineq → ℝ)
    (c : κ → ℝ) (d : ℝ) (hb : 0 ≤ b)
    (hub : ∀ x : κ → ℝ, 0 ≤ x → E.mulVec x = 0 → I.mulVec x ≤ b → c ⬝ᵥ x ≤ d) :
    ∃ (y : ι_eq → ℝ) (w : ι_ineq → ℝ),
      0 ≤ w ∧ c ≤ Eᵀ.mulVec y + Iᵀ.mulVec w ∧ w ⬝ᵥ b ≤ d := by
  classical
  let ι := κ ⊕ ι_eq ⊕ ι_eq ⊕ ι_ineq
  let A : Matrix ι κ ℝ := fun r k =>
    match r with
    | .inl k' => if k' = k then -1 else 0
    | .inr (.inl j) => E j k
    | .inr (.inr (.inl j)) => - E j k
    | .inr (.inr (.inr i)) => I i k
  let b_all : ι → ℝ := fun r =>
    match r with
    | .inl _ => 0
    | .inr (.inl _) => 0
    | .inr (.inr (.inl _)) => 0
    | .inr (.inr (.inr i)) => b i
  have hfeas : ∃ x : κ → ℝ, A.mulVec x ≤ b_all := by
    refine ⟨0, fun r => ?_⟩
    rw [Matrix.mulVec_zero]
    rcases r with k | j | j | i
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact hb i
  have hub_all : ∀ x : κ → ℝ, A.mulVec x ≤ b_all → c ⬝ᵥ x ≤ d := by
    intro x hx
    apply hub x
    · intro k
      change 0 ≤ x k
      have hk := hx (.inl k)
      unfold Matrix.mulVec dotProduct A b_all at hk
      simp only [ite_mul, neg_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at hk
      linarith
    · ext j
      change (E.mulVec x) j = 0
      have hj1 := hx (.inr (.inl j))
      have hj2 := hx (.inr (.inr (.inl j)))
      change (E.mulVec x) j ≤ 0 at hj1
      have hj2' : - (E.mulVec x) j ≤ 0 := by
        simpa [Matrix.mulVec, dotProduct, A, b_all, neg_mul, Finset.sum_neg_distrib] using hj2
      linarith
    · intro i
      exact hx (.inr (.inr (.inr i)))
  obtain ⟨p, hp_nn, hp_eq, hp_ub⟩ := farkas_inequality_form_fintype₂ A b_all c d hfeas hub_all
  let y : ι_eq → ℝ := fun j => p (.inr (.inl j)) - p (.inr (.inr (.inl j)))
  let w : ι_ineq → ℝ := fun i => p (.inr (.inr (.inr i)))
  refine ⟨y, w, fun i => hp_nn (.inr (.inr (.inr i))), ?_, ?_⟩
  · intro k
    change c k ≤ (Eᵀ.mulVec y) k + (Iᵀ.mulVec w) k
    have hk := (congrFun hp_eq k).symm
    have hsum : (Aᵀ.mulVec p) k =
        - p (.inl k) + (Eᵀ.mulVec y) k + (Iᵀ.mulVec w) k := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      dsimp only [A, y, w]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [ite_mul, neg_mul, one_mul, zero_mul,
        Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        mul_sub, Finset.sum_sub_distrib]
      ring
    have hp_k : 0 ≤ p (.inl k) := hp_nn (.inl k)
    linarith
  · have hdot : p ⬝ᵥ b_all = w ⬝ᵥ b := by
      unfold dotProduct b_all w
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp
    rwa [← hdot]

private abbrev PairV (V : Type) := {p : V × V // p.1 ≠ p.2}

private lemma sum_pair_eq_sum_pairV {M : Type*} [AddCommMonoid M]
    (F : V → V → M) (hdiag : ∀ s, F s s = 0) :
    ∑ s : V, ∑ t : V, F s t = ∑ st : PairV V, F st.1.1 st.1.2 := by
  rw [← Fintype.sum_prod_type' F]
  have hsub : ∑ st : PairV V, F st.1.1 st.1.2 =
      ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ≠ p.2), F p.1 p.2 := by
    refine Finset.sum_bij (fun (st : PairV V) _ => st.1) ?_ ?_ ?_ ?_
    · intro st _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, st.2⟩
    · intro st₁ _ st₂ _ h; exact Subtype.ext h
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨_, hp_ne⟩
      exact ⟨⟨p, hp_ne⟩, Finset.mem_univ _, rfl⟩
    · intro st _; rfl
  rw [hsub, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases p with ⟨s, t⟩
  by_cases hst : s = t
  · subst hst
    simp [hdiag s]
  · simp [hst]

private def IsGoodWalk (L : ℕ) (s t : V) (p : Fin L × (Fin (L + 1) → V)) : Prop :=
  p.2 0 = s ∧
  p.2 ⟨p.1.1 + 1, Nat.add_lt_add_right p.1.2 1⟩ = t ∧
  ∀ h : Fin (L + 1), h.1 < p.1.1 + 1 → p.2 h ≠ t

private instance (L : ℕ) (s t : V) : DecidablePred (IsGoodWalk L s t) := by
  intro p
  unfold IsGoodWalk
  infer_instance

private abbrev GoodWalk (L : ℕ) (s t : V) :=
  {p : Fin L × (Fin (L + 1) → V) // IsGoodWalk L s t p}

private def unitWalkFlow {L : ℕ} {s t : V} (w : GoodWalk L s t) (h : ℕ) (i j : V) : ℝ :=
  if hh : h < w.1.1.1 + 1 then
    if w.1.2 ⟨h, by omega⟩ = i ∧ w.1.2 ⟨h + 1, by omega⟩ = j then 1 else 0
  else 0

private lemma unitWalkFlow_nonneg {L : ℕ} {s t : V} (w : GoodWalk L s t) (h : ℕ) (i j : V) :
    0 ≤ unitWalkFlow w h i j := by
  unfold unitWalkFlow
  split_ifs <;> norm_num

private lemma unitWalkFlow_eq_zero_of_le {L : ℕ} {s t : V} (w : GoodWalk L s t)
    {h : ℕ} (hh : L ≤ h) (i j : V) :
    unitWalkFlow w h i j = 0 := by
  unfold unitWalkFlow
  have hlt := w.1.1.2
  exact dif_neg (by omega)

private lemma sum_unitWalkFlow_out {L : ℕ} {s t : V} (w : GoodWalk L s t) (h : ℕ) (u : V) :
    ∑ j : V, unitWalkFlow w h u j =
      if hh : h < w.1.1.1 + 1 then (if w.1.2 ⟨h, by omega⟩ = u then 1 else 0) else 0 := by
  unfold unitWalkFlow
  split_ifs with hh hvu
  · simp [hvu]
  · simp [hvu]
  · simp

private lemma sum_unitWalkFlow_in {L : ℕ} {s t : V} (w : GoodWalk L s t) (h : ℕ) (u : V) :
    ∑ i : V, unitWalkFlow w h i u =
      if hh : h < w.1.1.1 + 1 then (if w.1.2 ⟨h + 1, by omega⟩ = u then 1 else 0) else 0 := by
  unfold unitWalkFlow
  split_ifs with hh hvu
  · simp [hvu]
  · simp [hvu]
  · simp

private lemma sum_unitWalkFlow_zero {L : ℕ} {s t : V} (w : GoodWalk L s t) (u : V) :
    ∑ j : V, unitWalkFlow w 0 u j = if u = s then 1 else 0 := by
  rw [sum_unitWalkFlow_out, dif_pos (Nat.succ_pos _)]
  have h0 : w.1.2 ⟨0, by omega⟩ = s := w.2.1
  rw [h0]
  by_cases hus : u = s
  · simp [hus]
  · simp [hus, Ne.symm hus]

private lemma sum_unitWalkFlow_succ {L : ℕ} {s t : V} (w : GoodWalk L s t)
    {h : ℕ} (hh : h + 1 < L) (u : V) :
    ∑ j : V, unitWalkFlow w (h + 1) u j =
      if u = t then 0 else ∑ i : V, unitWalkFlow w h i u := by
  rw [sum_unitWalkFlow_out, sum_unitWalkFlow_in]
  rcases lt_trichotomy (h + 1) (w.1.1.1 + 1) with hlt | heq | hgt
  · have hh_lt : h < w.1.1.1 + 1 := by omega
    rw [dif_pos hlt, dif_pos hh_lt]
    by_cases hut : u = t
    · subst hut
      have hne : w.1.2 ⟨h + 1, by omega⟩ ≠ u := w.2.2.2 ⟨h + 1, by omega⟩ hlt
      simp [hne]
    · simp [hut]
  · have hh_lt : h < w.1.1.1 + 1 := by omega
    have hnot : ¬ (h + 1 < w.1.1.1 + 1) := by omega
    rw [dif_neg hnot, dif_pos hh_lt]
    by_cases hut : u = t
    · simp [hut]
    · have hlast : w.1.2 ⟨h + 1, by omega⟩ = t := by
        have hidx : (⟨h + 1, by omega⟩ : Fin (L + 1)) = ⟨w.1.1.1 + 1, by omega⟩ := by
          ext; exact heq
        rw [hidx]
        exact w.2.2.1
      rw [if_neg hut, hlast, if_neg (Ne.symm hut)]
  · have hnot1 : ¬ (h + 1 < w.1.1.1 + 1) := by omega
    have hnot2 : ¬ (h < w.1.1.1 + 1) := by omega
    rw [dif_neg hnot1, dif_neg hnot2, ite_self]

private lemma sum_unitWalkFlow_sink_out {L : ℕ} {s t : V} (w : GoodWalk L s t) (h : ℕ) :
    ∑ j : V, unitWalkFlow w h t j = 0 := by
  rw [sum_unitWalkFlow_out]
  split_ifs with hh hvt
  · exfalso; exact w.2.2.2 ⟨h, by omega⟩ hh hvt
  · rfl
  · rfl

private lemma sum_unitWalkFlow_last {L : ℕ} {s t : V} (w : GoodWalk L s t)
    {h : ℕ} (hh : h + 1 = L) {u : V} (hut : u ≠ t) :
    ∑ i : V, unitWalkFlow w h i u = 0 := by
  rw [sum_unitWalkFlow_in]
  split_ifs with hh_lt hvu
  · exfalso
    have hm_lt := w.1.1.2
    have heq : h + 1 = w.1.1.1 + 1 := by omega
    have hlast : w.1.2 ⟨h + 1, by omega⟩ = t := by
      have hidx : (⟨h + 1, by omega⟩ : Fin (L + 1)) = ⟨w.1.1.1 + 1, by omega⟩ := by
        ext; exact heq
      rw [hidx]
      exact w.2.2.1
    exact hut (hvu.symm.trans hlast)
  · rfl
  · rfl

private lemma sum_unitWalkFlow_sink_in {L : ℕ} {s t : V} (w : GoodWalk L s t) :
    ∑ h ∈ Finset.range L, ∑ i : V, unitWalkFlow w h i t = 1 := by
  have hm_lt : w.1.1.1 < L := w.1.1.2
  have hterm : ∀ h ∈ Finset.range L,
      ∑ i : V, unitWalkFlow w h i t = if h = w.1.1.1 then 1 else 0 := by
    intro h hh
    have hhL : h < L := Finset.mem_range.mp hh
    rw [sum_unitWalkFlow_in]
    rcases lt_trichotomy h w.1.1.1 with hlt | heq | hgt
    · have hh1 : h < w.1.1.1 + 1 := by omega
      have hne : w.1.2 ⟨h + 1, by omega⟩ ≠ t := w.2.2.2 ⟨h + 1, by omega⟩ (by simp; omega)
      rw [dif_pos hh1, if_neg hne, if_neg (by omega)]
    · subst heq
      have hh1 : w.1.1.1 < w.1.1.1 + 1 := Nat.lt_succ_self _
      rw [dif_pos hh1, if_pos w.2.2.1, if_pos rfl]
    · have hh1 : ¬ (h < w.1.1.1 + 1) := by omega
      rw [dif_neg hh1, if_neg (by omega)]
  rw [Finset.sum_congr rfl hterm]
  simp [Finset.mem_range.mpr hm_lt]

private abbrev WalkVar (V : Type) (L : ℕ) :=
  Unit ⊕ (Σ st : PairV V, GoodWalk L st.1.1 st.1.2)

private def flowOfWalkVar (L : ℕ) (x : WalkVar V L → ℝ) (s t : V) (h : ℕ) (i j : V) : ℝ :=
  if hst : s ≠ t then
    ∑ w : GoodWalk L s t, x (.inr ⟨⟨(s, t), hst⟩, w⟩) * unitWalkFlow w h i j
  else 0

private lemma isShortConcurrentFlow_of_walkVar (N : Network V) (L : ℕ) (x : WalkVar V L → ℝ)
    (hx_nn : ∀ col, 0 ≤ x col)
    (hx_dem : ∀ st : PairV V,
      ∑ w : GoodWalk L st.1.1 st.1.2, x (.inr ⟨st, w⟩) =
        x (.inl ()) * uniformDemand st.1.1 st.1.2)
    (hx_cap : ∀ i j : V,
      ∑ st : PairV V, ∑ w : GoodWalk L st.1.1 st.1.2,
        x (.inr ⟨st, w⟩) * (∑ h ∈ Finset.range L, (unitWalkFlow w h i j + unitWalkFlow w h j i)) ≤
          N.C i j) :
    IsShortConcurrentFlow N uniformDemand L (flowOfWalkVar L x) (x (.inl ())) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t h i j
    unfold flowOfWalkVar
    split_ifs with hst
    · exact Finset.sum_nonneg fun w _ => mul_nonneg (hx_nn _) (unitWalkFlow_nonneg w h i j)
    · exact le_rfl
  · intro s t h i j hh
    unfold flowOfWalkVar
    split_ifs with hst
    · refine Finset.sum_eq_zero fun w _ => ?_
      rw [unitWalkFlow_eq_zero_of_le w hh, mul_zero]
    · rfl
  · intro s h i j
    unfold flowOfWalkVar
    exact dif_neg (not_not.mpr rfl)
  · intro s t hst v
    have hpull : ∑ j : V, flowOfWalkVar L x s t 0 v j =
        ∑ w : GoodWalk L s t, x (.inr ⟨⟨(s, t), hst⟩, w⟩) * ∑ j : V, unitWalkFlow w 0 v j := by
      simp only [flowOfWalkVar, dif_pos hst, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hpull]
    simp only [sum_unitWalkFlow_zero]
    by_cases hvs : v = s
    · subst hvs
      simp only [↓reduceIte, mul_one]
      exact hx_dem ⟨(v, t), hst⟩
    · simp [hvs]
  · intro s t h hst hh v
    have hpull_out : ∑ j : V, flowOfWalkVar L x s t (h + 1) v j =
        ∑ w : GoodWalk L s t, x (.inr ⟨⟨(s, t), hst⟩, w⟩) * ∑ j : V, unitWalkFlow w (h + 1) v j := by
      simp only [flowOfWalkVar, dif_pos hst, Finset.mul_sum]
      exact Finset.sum_comm
    have hpull_in : ∑ i : V, flowOfWalkVar L x s t h i v =
        ∑ w : GoodWalk L s t, x (.inr ⟨⟨(s, t), hst⟩, w⟩) * ∑ i : V, unitWalkFlow w h i v := by
      simp only [flowOfWalkVar, dif_pos hst, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hpull_out, hpull_in]
    by_cases hvt : v = t
    · subst hvt
      simp [sum_unitWalkFlow_succ _ hh]
    · rw [if_neg hvt]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [sum_unitWalkFlow_succ w hh v, if_neg hvt]
  · intro s t h hst _
    have hpull : ∑ j : V, flowOfWalkVar L x s t h t j =
        ∑ w : GoodWalk L s t, x (.inr ⟨⟨(s, t), hst⟩, w⟩) * ∑ j : V, unitWalkFlow w h t j := by
      simp only [flowOfWalkVar, dif_pos hst, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hpull]
    simp [sum_unitWalkFlow_sink_out]
  · intro s t h hst hh v hvt
    have hpull : ∑ i : V, flowOfWalkVar L x s t h i v =
        ∑ w : GoodWalk L s t, x (.inr ⟨⟨(s, t), hst⟩, w⟩) * ∑ i : V, unitWalkFlow w h i v := by
      simp only [flowOfWalkVar, dif_pos hst, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hpull]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [sum_unitWalkFlow_last w hh hvt, mul_zero]
  · intro s t hst
    have hpull : ∑ h ∈ Finset.range L, ∑ i : V, flowOfWalkVar L x s t h i t =
        ∑ w : GoodWalk L s t, x (.inr ⟨⟨(s, t), hst⟩, w⟩) *
          ∑ h ∈ Finset.range L, ∑ i : V, unitWalkFlow w h i t := by
      have h1 : ∀ h, ∑ i : V, flowOfWalkVar L x s t h i t =
          ∑ w : GoodWalk L s t, x (.inr ⟨⟨(s, t), hst⟩, w⟩) * ∑ i : V, unitWalkFlow w h i t := by
        intro h
        simp only [flowOfWalkVar, dif_pos hst, Finset.mul_sum]
        exact Finset.sum_comm
      simp_rw [h1, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hpull]
    simp only [sum_unitWalkFlow_sink_in, mul_one]
    exact hx_dem ⟨(s, t), hst⟩
  · intro i j
    have hconv : (∑ s : V, ∑ t : V, ∑ h ∈ Finset.range L,
        (flowOfWalkVar L x s t h i j + flowOfWalkVar L x s t h j i)) =
        ∑ st : PairV V, ∑ w : GoodWalk L st.1.1 st.1.2,
          x (.inr ⟨st, w⟩) * (∑ h ∈ Finset.range L, (unitWalkFlow w h i j + unitWalkFlow w h j i)) := by
      rw [sum_pair_eq_sum_pairV (fun s t => ∑ h ∈ Finset.range L,
        (flowOfWalkVar L x s t h i j + flowOfWalkVar L x s t h j i))]
      · refine Finset.sum_congr rfl fun st _ => ?_
        rcases st with ⟨⟨s, t⟩, hst⟩
        simp only [flowOfWalkVar, dif_pos hst, ← Finset.sum_add_distrib, ← mul_add, Finset.mul_sum]
        exact Finset.sum_comm
      · intro s
        simp [flowOfWalkVar]
    rw [hconv]
    exact hx_cap i j

private lemma exists_goodWalk_seq_of_walk {N : Network V} {d : V → V → ℝ}
    (hd : IsDistanceFunction d) {u t : V} (q : N.graph.Walk u t) (hut : u ≠ t) :
    ∃ (k : ℕ) (v : ℕ → V),
      k < q.length ∧
      v 0 = u ∧
      v (k + 1) = t ∧
      (∀ h < k + 1, v h ≠ t) ∧
      ∑ h ∈ Finset.range (k + 1), d (v h) (v (h + 1)) ≤ walkLen d q := by
  induction q with
  | nil => exact absurd rfl hut
  | @cons u w t hadj q' ih =>
    by_cases hwt : w = t
    · subst hwt
      refine ⟨0, fun n => if n = 0 then u else w, ?_, rfl, rfl, ?_, ?_⟩
      · simp
      · intro h hh
        have h0 : h = 0 := by omega
        subst h0
        exact hut
      · have h0 : ∑ h ∈ Finset.range (0 + 1),
            d (if h = 0 then u else w) (if h + 1 = 0 then u else w) = d u w := by simp
        rw [h0]
        have hq'_nn : 0 ≤ walkLen d q' := by
          unfold walkLen
          apply List.sum_nonneg
          intro x hx
          rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
          exact hd.1 a.fst a.snd
        have hcons : walkLen d (SimpleGraph.Walk.cons hadj q') = d u w + walkLen d q' := by
          unfold walkLen
          simp
        linarith
    · obtain ⟨k', v', hk'_len, hv'0, hv'last, hv'ne, hv'cost⟩ := ih hwt
      let v : ℕ → V := fun n =>
        match n with
        | 0 => u
        | n' + 1 => v' n'
      refine ⟨k' + 1, v, ?_, rfl, hv'last, ?_, ?_⟩
      · simp [hk'_len]
      · intro h hh
        cases h with
        | zero => exact hut
        | succ h' => exact hv'ne h' (by omega)
      · rw [Finset.sum_range_succ']
        change (∑ x ∈ Finset.range (k' + 1), d (v' x) (v' (x + 1))) + d u (v' 0) ≤
          walkLen d (SimpleGraph.Walk.cons hadj q')
        rw [hv'0]
        unfold walkLen at hv'cost ⊢
        simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
        linarith

private lemma exists_goodWalk_of_walk {N : Network V} {d : V → V → ℝ}
    (hd : IsDistanceFunction d) {L : ℕ} {s t : V} (hst : s ≠ t)
    (q : N.graph.Walk s t) (hq : (q.length : ℝ) ≤ (L : ℝ)) :
    ∃ w : GoodWalk L s t,
      ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, unitWalkFlow w h i j * d i j ≤ walkLen d q := by
  have hq_nat : q.length ≤ L := by exact_mod_cast hq
  obtain ⟨k, v, hk_len, hv0, hvlast, hvne, hvcost⟩ := exists_goodWalk_seq_of_walk hd q hst
  have hkL : k < L := lt_of_lt_of_le hk_len hq_nat
  let w : GoodWalk L s t :=
    ⟨(⟨k, hkL⟩, fun i : Fin (L + 1) => v i.1), hv0, hvlast, fun h hh => hvne h.1 hh⟩
  refine ⟨w, ?_⟩
  have hsum_eq :
      ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, unitWalkFlow w h i j * d i j =
        ∑ h ∈ Finset.range (k + 1), d (v h) (v (h + 1)) := by
    have hstep : ∀ h ∈ Finset.range L,
        ∑ i : V, ∑ j : V, unitWalkFlow w h i j * d i j =
          if h < k + 1 then d (v h) (v (h + 1)) else 0 := by
      intro h hh
      unfold unitWalkFlow
      change (∑ i : V, ∑ j : V,
        (if hh' : h < k + 1 then
          if v h = i ∧ v (h + 1) = j then (1 : ℝ) else 0
        else 0) * d i j) = if h < k + 1 then d (v h) (v (h + 1)) else 0
      split_ifs with hh'
      · have h_inner : ∀ i : V,
            (∑ j : V, (if v h = i ∧ v (h + 1) = j then (1 : ℝ) else 0) * d i j) =
              if v h = i then d i (v (h + 1)) else 0 := by
          intro i
          by_cases hi : v h = i <;> simp [hi]
        simp_rw [h_inner]
        simp
      · simp
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
    have hfilt : (Finset.range L).filter (fun h => h < k + 1) = Finset.range (k + 1) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilt]
  rw [hsum_eq]
  exact hvcost

private lemma dual_attainment (N : Network V) (hn : 2 ≤ Fintype.card V)
    {L : ℕ} (hL : 0 < L) :
    ∃ d : V → V → ℝ, IsDistanceFunction d ∧
      SatisfiesShortConstraint N d L ∧
      totalWeight N d = maxShortFlow N uniformDemand L := by
  let lam_star := maxShortFlow N uniformDemand L
  have hbdd := (primal_attainment N hn L).2.2
  let E : Matrix (PairV V) (WalkVar V L) ℝ := fun st col =>
    match col with
    | .inl () => uniformDemand st.1.1 st.1.2
    | .inr ⟨st', _⟩ => if st = st' then -1 else 0
  let I : Matrix (V × V) (WalkVar V L) ℝ := fun uv col =>
    match col with
    | .inl () => 0
    | .inr ⟨_, w⟩ => ∑ h ∈ Finset.range L, (unitWalkFlow w h uv.1 uv.2 + unitWalkFlow w h uv.2 uv.1)
  let b : V × V → ℝ := fun uv => N.C uv.1 uv.2
  let c : WalkVar V L → ℝ := fun col =>
    match col with
    | .inl () => 1
    | .inr _ => 0
  have hb : 0 ≤ b := fun uv => N.C_nonneg uv.1 uv.2
  have hub : ∀ x : WalkVar V L → ℝ, 0 ≤ x → E.mulVec x = 0 → I.mulVec x ≤ b → c ⬝ᵥ x ≤ lam_star := by
    intro x hx_nn hx_eq hx_ineq
    have h_dot : c ⬝ᵥ x = x (.inl ()) := by
      unfold dotProduct c
      rw [Fintype.sum_sum_type]
      simp
    rw [h_dot]
    have hx_dem : ∀ st : PairV V,
        ∑ w : GoodWalk L st.1.1 st.1.2, x (.inr ⟨st, w⟩) =
          x (.inl ()) * uniformDemand st.1.1 st.1.2 := by
      intro st
      have hst := congrFun hx_eq st
      change (E.mulVec x) st = 0 at hst
      unfold Matrix.mulVec dotProduct E at hst
      rw [Fintype.sum_sum_type, Fintype.sum_sigma] at hst
      simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
        ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_neg_distrib,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte] at hst
      linarith
    have hx_cap : ∀ i j : V,
        ∑ st : PairV V, ∑ w : GoodWalk L st.1.1 st.1.2,
          x (.inr ⟨st, w⟩) * (∑ h ∈ Finset.range L, (unitWalkFlow w h i j + unitWalkFlow w h j i)) ≤
            N.C i j := by
      intro i j
      have hij := hx_ineq (i, j)
      unfold Matrix.mulVec dotProduct I b at hij
      rw [Fintype.sum_sum_type, Fintype.sum_sigma] at hij
      simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
        zero_mul, zero_add] at hij
      refine le_trans (le_of_eq ?_) hij
      refine Finset.sum_congr rfl fun st _ => Finset.sum_congr rfl fun w _ => mul_comm _ _
    have hflow := isShortConcurrentFlow_of_walkVar N L x hx_nn hx_dem hx_cap
    exact le_csSup hbdd ⟨hx_nn (.inl ()), _, hflow⟩
  obtain ⟨y, w_cap, hw_nn, hc_le, hw_ub⟩ := farkas_standard_form E I b c lam_star hb hub
  let d : V → V → ℝ := fun u v => w_cap (u, v) + w_cap (v, u)
  have hd : IsDistanceFunction d := by
    refine ⟨fun u v => add_nonneg (hw_nn (u, v)) (hw_nn (v, u)), fun u v => add_comm _ _⟩
  have hW_le : totalWeight N d ≤ lam_star := by
    have hW_eq : totalWeight N d = w_cap ⬝ᵥ b := by
      unfold totalWeight dotProduct d b
      rw [Fintype.sum_prod_type]
      have hsymm :
          ∑ u : V, ∑ v : V, N.C u v * w_cap (v, u) =
            ∑ u : V, ∑ v : V, N.C u v * w_cap (u, v) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [N.C_symm v u]
      simp only [mul_add, Finset.sum_add_distrib]
      rw [hsymm]
      have hcomm :
          ∑ u : V, ∑ v : V, N.C u v * w_cap (u, v) =
            ∑ u : V, ∑ v : V, w_cap (u, v) * N.C u v :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => mul_comm _ _
      linarith
    rwa [hW_eq]
  have hy_sum : 1 ≤ ∑ st : PairV V, (1 / 2 : ℝ) * y st := by
    have h_inl := hc_le (.inl ())
    change 1 ≤ (Eᵀ.mulVec y) (.inl ()) + (Iᵀ.mulVec w_cap) (.inl ()) at h_inl
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at h_inl
    dsimp only [E, I] at h_inl
    simp only [zero_mul, Finset.sum_const_zero, add_zero] at h_inl
    refine h_inl.trans (le_of_eq (Finset.sum_congr rfl fun st _ => ?_))
    rw [uniformDemand, if_neg st.2]
  have hy_walk : ∀ (st : PairV V) (w : GoodWalk L st.1.1 st.1.2),
      y st ≤ ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, unitWalkFlow w h i j * d i j := by
    intro st w
    have h_inr := hc_le (.inr ⟨st, w⟩)
    change 0 ≤ (Eᵀ.mulVec y) (.inr ⟨st, w⟩) + (Iᵀ.mulVec w_cap) (.inr ⟨st, w⟩) at h_inr
    have hE : (Eᵀ.mulVec y) (.inr ⟨st, w⟩) = - y st := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      dsimp only [E]
      simp [ite_mul]
    have hI : (Iᵀ.mulVec w_cap) (.inr ⟨st, w⟩) =
        ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, unitWalkFlow w h i j * d i j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      dsimp only [I, d]
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_mul, add_mul, mul_add, Finset.sum_add_distrib]
      have hpull1 :
          ∑ i : V, ∑ j : V, ∑ h ∈ Finset.range L, unitWalkFlow w h i j * w_cap (i, j) =
            ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, unitWalkFlow w h i j * w_cap (i, j) := by
        have h1 : ∀ i : V, ∑ j : V, ∑ h ∈ Finset.range L, unitWalkFlow w h i j * w_cap (i, j) =
            ∑ h ∈ Finset.range L, ∑ j : V, unitWalkFlow w h i j * w_cap (i, j) :=
          fun _ => Finset.sum_comm
        simp_rw [h1]
        exact Finset.sum_comm
      have hpull2 :
          ∑ i : V, ∑ j : V, ∑ h ∈ Finset.range L, unitWalkFlow w h j i * w_cap (i, j) =
            ∑ h ∈ Finset.range L, ∑ i : V, ∑ j : V, unitWalkFlow w h i j * w_cap (j, i) := by
        rw [Finset.sum_comm]
        have h1 : ∀ i : V, ∑ j : V, ∑ h ∈ Finset.range L, unitWalkFlow w h i j * w_cap (j, i) =
            ∑ h ∈ Finset.range L, ∑ j : V, unitWalkFlow w h i j * w_cap (j, i) :=
          fun _ => Finset.sum_comm
        simp_rw [h1]
        exact Finset.sum_comm
      rw [hpull1, hpull2]
    linarith
  have hshort : SatisfiesShortConstraint N d L := by
    unfold SatisfiesShortConstraint
    have hst_le : ∀ st : PairV V,
        ENNReal.ofReal (y st) ≤ distL N d (L : ℝ) st.1.1 st.1.2 := by
      intro st
      unfold distL
      refine le_iInf₂ fun q hq => ?_
      obtain ⟨w, hw⟩ := exists_goodWalk_of_walk hd st.2 q hq
      exact ENNReal.ofReal_le_ofReal ((hy_walk st w).trans hw)
    have h_sum_le : ∀ (s : Finset (PairV V)),
        ENNReal.ofReal (∑ st ∈ s, (1 / 2 : ℝ) * y st) ≤
          ∑ st ∈ s, ENNReal.ofReal ((1 / 2 : ℝ) * y st) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        refine ENNReal.ofReal_add_le.trans ?_
        gcongr
    have h1 : (1 : ENNReal) ≤ (1 / 2 : ENNReal) * ∑ st : PairV V, ENNReal.ofReal (y st) := by
      have h_ofReal := ENNReal.ofReal_le_ofReal hy_sum
      rw [ENNReal.ofReal_one] at h_ofReal
      refine h_ofReal.trans ((h_sum_le Finset.univ).trans ?_)
      have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      rw [hhalf, Finset.mul_sum]
      refine Finset.sum_le_sum fun st _ => ?_
      rw [ENNReal.ofReal_mul (by norm_num)]
    have h2 : ∑ st : PairV V, ENNReal.ofReal (y st) ≤
        ∑ s : V, ∑ t : V, distL N d (L : ℝ) s t := by
      rw [sum_pair_eq_sum_pairV (fun s t => distL N d (L : ℝ) s t)
        (fun s => distL_self_zero N d (Nat.cast_nonneg L) s)]
      exact Finset.sum_le_sum fun st _ => hst_le st
    refine h1.trans ?_
    gcongr
  refine ⟨d, hd, hshort, le_antisymm hW_le (weak_duality N hn L d hd hshort)⟩

/-- The LP dual for the hop-restricted uniform multicommodity flow problem, §2.5, p. 808. -/
theorem short_path_duality {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N) (L : ℕ) :
    (∀ d : V → V → ℝ, IsDistanceFunction d → SatisfiesShortConstraint N d L →
      maxShortFlow N uniformDemand L ≤ totalWeight N d) ∧
    (0 < L → ∃ f : V → V → ℕ → V → V → ℝ,
      IsShortConcurrentFlow N uniformDemand L f (maxShortFlow N uniformDemand L)) ∧
    (0 < L → ∃ d : V → V → ℝ, IsDistanceFunction d ∧
      SatisfiesShortConstraint N d L ∧
      totalWeight N d = maxShortFlow N uniformDemand L) :=
  ⟨weak_duality N hn L, fun _ => (primal_attainment N hn L).1, dual_attainment N hn⟩

end LeightonRao.ShortPaths

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : LeightonRao.ShortPaths.Network V) (hn : 2 ≤ Fintype.card V)
    (hconn : LeightonRao.ShortPaths.IsConnectedNet N) (L : ℕ) :
    (∀ d : V → V → ℝ, LeightonRao.ShortPaths.IsDistanceFunction d →
      LeightonRao.ShortPaths.SatisfiesShortConstraint N d L →
      LeightonRao.ShortPaths.maxShortFlow N LeightonRao.ShortPaths.uniformDemand L ≤
        LeightonRao.ShortPaths.totalWeight N d) ∧
    (0 < L → ∃ f : V → V → ℕ → V → V → ℝ,
      LeightonRao.ShortPaths.IsShortConcurrentFlow N LeightonRao.ShortPaths.uniformDemand L f
        (LeightonRao.ShortPaths.maxShortFlow N LeightonRao.ShortPaths.uniformDemand L)) ∧
    (0 < L → ∃ d : V → V → ℝ, LeightonRao.ShortPaths.IsDistanceFunction d ∧
      LeightonRao.ShortPaths.SatisfiesShortConstraint N d L ∧
      LeightonRao.ShortPaths.totalWeight N d =
        LeightonRao.ShortPaths.maxShortFlow N LeightonRao.ShortPaths.uniformDemand L) :=
  LeightonRao.ShortPaths.short_path_duality N hn hconn L
