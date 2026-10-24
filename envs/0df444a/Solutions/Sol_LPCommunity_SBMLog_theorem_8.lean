-- Prove2me | solution 1 for LPCommunity.SBMLog.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T09:57:49.030772+00:00
-- url     : https://prove2.me/submissions/49e9fa69-48fc-45f4-ad79-7064a5568171

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting
import Definitions.Def_LPCommunity_SBMLog_RandomGraphs

open Finset
open scoped Classical

namespace LPSBMLog8Aux

open LPCommunity.SBMRecovery LPCommunity.MinBisect LPCommunity.LPRecovery

lemma clamp01_nonneg (p : ℝ) : 0 ≤ clamp01 p := le_max_left _ _
lemma clamp01_le_one (p : ℝ) : clamp01 p ≤ 1 := max_le zero_le_one (min_le_left _ _)
lemma clamp01_le (p : ℝ) (hp : 0 ≤ p) : clamp01 p ≤ p := max_le hp (min_le_right _ _)
lemma clamp01_eq (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : clamp01 p = p := by
  simp [clamp01, h0, h1]

/-- edge set of a graph, as a subset of `pairs n`. -/
noncomputable def toSet {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) :=
  (pairs n).filter (fun p => G.Adj p.1 p.2)

noncomputable def ofSet {n : ℕ} (A : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => (i, j) ∈ A)

lemma mem_pairs {n : ℕ} (p : Fin n × Fin n) : p ∈ pairs n ↔ p.1 < p.2 := by
  simp [pairs]

lemma sum_graphs {n : ℕ} (F : Finset (Fin n × Fin n) → ℝ) :
    ∑ G : SimpleGraph (Fin n), F (toSet G) = ∑ A ∈ (pairs n).powerset, F A := by
  apply Finset.sum_nbij' toSet ofSet
  · intro G _; simp [toSet, Finset.filter_subset]
  · intro A _; simp
  · intro G _
    ext i j
    simp only [ofSet, toSet, SimpleGraph.fromRel_adj, Finset.mem_filter, mem_pairs]
    constructor
    · rintro ⟨_, (⟨_, h⟩ | ⟨_, h⟩)⟩
      · exact h
      · exact h.symm
    · intro h
      refine ⟨G.ne_of_adj h, ?_⟩
      rcases lt_trichotomy i j with hij | hij | hij
      · exact Or.inl ⟨hij, h⟩
      · exact absurd hij (G.ne_of_adj h)
      · exact Or.inr ⟨hij, h.symm⟩
  · intro A hA
    have hA' : A ⊆ pairs n := by simpa using hA
    ext p
    simp only [ofSet, toSet, SimpleGraph.fromRel_adj, Finset.mem_filter, mem_pairs]
    constructor
    · rintro ⟨hp, _, h | h⟩
      · exact h
      · have := (mem_pairs _).1 (hA' h); simp at this; exact absurd hp (not_lt.2 this.le)
    · intro h
      have hp := (mem_pairs _).1 (hA' h)
      exact ⟨hp, ne_of_lt hp, Or.inl h⟩
  · intro G _; rfl

lemma expect_prod {n : ℕ} (r : Fin n → Fin n → ℝ) (g : Fin n × Fin n → ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * ∏ p ∈ pairs n, (if G.Adj p.1 p.2 then g p else 1)
      = ∏ p ∈ pairs n, (clamp01 (r p.1 p.2) * g p + (1 - clamp01 (r p.1 p.2))) := by
  set c : Fin n × Fin n → ℝ := fun p => clamp01 (r p.1 p.2)
  have h1 : ∀ G : SimpleGraph (Fin n), edgeWeight G r * ∏ p ∈ pairs n,
      (if G.Adj p.1 p.2 then g p else 1)
      = (fun A => ∏ p ∈ pairs n, (if p ∈ A then c p * g p else 1 - c p)) (toSet G) := by
    intro G
    simp only [edgeWeight, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [toSet, Finset.mem_filter, hp, true_and, c]
    split_ifs <;> ring
  simp_rw [h1]
  rw [sum_graphs (fun A => ∏ p ∈ pairs n, (if p ∈ A then c p * g p else 1 - c p))]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro A hA
  have hA' : A ⊆ pairs n := by simpa using hA
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext p; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hA' h, h⟩⟩
  · congr 1; ext p; simp [Finset.mem_sdiff]

lemma edgeWeight_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → Fin n → ℝ) :
    0 ≤ edgeWeight G r := by
  unfold edgeWeight
  apply Finset.prod_nonneg
  intro p _
  split_ifs
  · exact clamp01_nonneg _
  · linarith [clamp01_le_one (r p.1 p.2)]

lemma sum_edgeWeight {n : ℕ} (r : Fin n → Fin n → ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r = 1 := by
  have := expect_prod r (fun _ => 1)
  simp only [ite_self, Finset.prod_const_one, mul_one] at this
  rw [this]
  apply Finset.prod_eq_one
  intro p _; ring

lemma expect_prod_le {n : ℕ} (r : Fin n → Fin n → ℝ) (g : Fin n × Fin n → ℝ)
    (hg : ∀ p, 0 ≤ g p) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * ∏ p ∈ pairs n, (if G.Adj p.1 p.2 then g p else 1)
      ≤ Real.exp (∑ p ∈ pairs n, clamp01 (r p.1 p.2) * (g p - 1)) := by
  rw [expect_prod, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p _
    have := clamp01_nonneg (r p.1 p.2)
    have := clamp01_le_one (r p.1 p.2)
    have := hg p
    nlinarith
  · intro p _
    have := Real.add_one_le_exp (clamp01 (r p.1 p.2) * (g p - 1))
    linarith

lemma markov {n : ℕ} (r : Fin n → Fin n → ℝ) (A : SimpleGraph (Fin n) → Prop)
    (Y : SimpleGraph (Fin n) → ℝ) (t : ℝ) (ht : 0 < t) (hY : ∀ G, 0 ≤ Y G)
    (hA : ∀ G, A G → t ≤ Y G) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if A G then 1 else 0)
      ≤ (∑ G : SimpleGraph (Fin n), edgeWeight G r * Y G) / t := by
  rw [le_div_iff₀ ht, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro G _
  have hw := edgeWeight_nonneg G r
  split_ifs with h
  · have := hA G h; nlinarith
  · have := hY G; nlinarith


section Det

open Matrix

variable {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ)

/-- truncated graph distance `min(K, dist_G)` (unreachable pairs get `K`). -/
noncomputable def T (i j : Fin n) : ℕ := (min (K : ℕ∞) (G.edist i j)).toNat

lemma T_cast (i j : Fin n) : ((T G K i j : ℕ) : ℕ∞) = min (K : ℕ∞) (G.edist i j) := by
  unfold T
  rw [ENat.natCast_toNat_eq_self]
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top K) (min_le_left _ _)

lemma T_le (i j : Fin n) : T G K i j ≤ K := by
  have h := T_cast G K i j
  have : ((T G K i j : ℕ) : ℕ∞) ≤ K := by rw [h]; exact min_le_left _ _
  exact_mod_cast this

lemma T_self (i : Fin n) : T G K i i = 0 := by
  unfold T; simp [SimpleGraph.edist_self]

lemma T_comm (i j : Fin n) : T G K i j = T G K j i := by
  unfold T; rw [SimpleGraph.edist_comm]

lemma T_triangle (i j k : Fin n) : T G K i j ≤ T G K i k + T G K k j := by
  have key : min (K : ℕ∞) (G.edist i j) ≤ min (K : ℕ∞) (G.edist i k) + min (K : ℕ∞) (G.edist k j) := by
    have h := G.edist_triangle (u := i) (v := k) (w := j)
    by_cases h1 : (K : ℕ∞) ≤ G.edist i k
    · calc min (K : ℕ∞) (G.edist i j) ≤ K := min_le_left _ _
        _ = min (K : ℕ∞) (G.edist i k) := (min_eq_left h1).symm
        _ ≤ _ := le_self_add
    by_cases h2 : (K : ℕ∞) ≤ G.edist k j
    · calc min (K : ℕ∞) (G.edist i j) ≤ K := min_le_left _ _
        _ = min (K : ℕ∞) (G.edist k j) := (min_eq_left h2).symm
        _ ≤ _ := le_add_self
    · push Not at h1 h2
      rw [min_eq_right h1.le, min_eq_right h2.le]
      exact (min_le_right _ _).trans h
  rw [← T_cast, ← T_cast, ← T_cast] at key
  exact_mod_cast key

lemma T_adj (hK : 1 ≤ K) {i j : Fin n} (h : G.Adj i j) : T G K i j = 1 := by
  unfold T
  rw [SimpleGraph.edist_eq_one_iff_adj.2 h]
  have : (1 : ℕ∞) ≤ K := by exact_mod_cast hK
  rw [min_eq_right this]; rfl

lemma T_lt {i j : Fin n} (hij : i ≠ j) (hT : T G K i j < K) :
    G.edist i j = (T G K i j : ℕ∞) ∧ 1 ≤ T G K i j := by
  have hc := T_cast G K i j
  have hlt : ((T G K i j : ℕ) : ℕ∞) < K := by exact_mod_cast hT
  have hd : G.edist i j < K := by
    by_contra hcon
    push Not at hcon
    rw [hc, min_eq_left hcon] at hlt
    exact lt_irrefl _ hlt
  have he : G.edist i j = (T G K i j : ℕ∞) := by rw [hc, min_eq_right hd.le]
  refine ⟨he, ?_⟩
  by_contra h0
  push Not at h0
  have : T G K i j = 0 := by omega
  rw [this] at he
  exact hij ((SimpleGraph.edist_eq_zero_iff (G := G)).1 (by simpa using he))

lemma pow_entry_nonneg (l : ℕ) (i j : Fin n) : 0 ≤ (G.adjMatrix ℝ ^ l) i j := by
  rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk]; exact Nat.cast_nonneg _

lemma pow_entry_ge_one {l : ℕ} {i j : Fin n} (h : G.edist i j = l) :
    1 ≤ (G.adjMatrix ℝ ^ l) i j := by
  rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_eq_coe h
  have : 0 < Fintype.card { p : G.Walk i j | p.length = l } :=
    Fintype.card_pos_iff.2 ⟨⟨w, hw⟩⟩
  exact_mod_cast this

lemma row_sum_le (D : ℝ) (hD : 0 ≤ D) (hdeg : ∀ v, (G.degree v : ℝ) ≤ D) (l : ℕ) (i : Fin n) :
    ∑ j, (G.adjMatrix ℝ ^ l) i j ≤ D ^ l := by
  have key : ∀ l : ℕ, ∀ i, ((G.adjMatrix ℝ ^ l) *ᵥ (fun _ => (1:ℝ))) i ≤ D ^ l := by
    intro l
    induction l with
    | zero => intro i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    | succ l ih =>
      intro i
      rw [pow_succ, ← Matrix.mulVec_mulVec]
      have h1 : ∀ u, (G.adjMatrix ℝ *ᵥ (fun _ => (1:ℝ))) u ≤ D := by
        intro u
        have := SimpleGraph.adjMatrix_mulVec_const_apply (G := G) (α := ℝ) (a := 1) (v := u)
        simp only [Function.const, mul_one] at this
        rw [show (fun _ : Fin n => (1:ℝ)) = Function.const (Fin n) (1:ℝ) from rfl, this]
        exact hdeg u
      calc ((G.adjMatrix ℝ ^ l) *ᵥ (G.adjMatrix ℝ *ᵥ (fun _ => (1:ℝ)))) i
          = ∑ u, (G.adjMatrix ℝ ^ l) i u * (G.adjMatrix ℝ *ᵥ (fun _ => (1:ℝ))) u := rfl
        _ ≤ ∑ u, (G.adjMatrix ℝ ^ l) i u * D := by
          apply Finset.sum_le_sum; intro u _
          exact mul_le_mul_of_nonneg_left (h1 u) (pow_entry_nonneg G l i u)
        _ = D * ((G.adjMatrix ℝ ^ l) *ᵥ (fun _ => (1:ℝ))) i := by
          simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm]
        _ ≤ D * D ^ l := mul_le_mul_of_nonneg_left (ih i) hD
        _ = D ^ (l + 1) := by ring
  have := key l i
  simpa [Matrix.mulVec, dotProduct] using this


lemma count_lt (n : ℕ) :
    ∑ i : Fin n, ∑ j : Fin n, (if i < j then (1:ℝ) else 0) = ((n:ℝ) ^ 2 - n) / 2 := by
  have hsw : ∑ i : Fin n, ∑ j : Fin n, (if j < i then (1:ℝ) else 0)
      = ∑ i : Fin n, ∑ j : Fin n, (if i < j then (1:ℝ) else 0) := Finset.sum_comm
  have hne : ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then (1:ℝ) else 0) = (n:ℝ) ^ 2 - n := by
    have : ∀ i : Fin n, ∑ j : Fin n, (if i ≠ j then (1:ℝ) else 0) = n - 1 := by
      intro i
      have h2 : ∑ j : Fin n, (if i ≠ j then (1:ℝ) else 0)
          = ∑ j : Fin n, (1 - if i = j then (1:ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro j _; split_ifs <;> simp_all
      rw [h2, Finset.sum_sub_distrib]; simp
    rw [Finset.sum_congr rfl (fun i _ => this i)]; simp; ring
  have hsplit : ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then (1:ℝ) else 0)
      = ∑ i : Fin n, ∑ j : Fin n, (if i < j then (1:ℝ) else 0)
        + ∑ i : Fin n, ∑ j : Fin n, (if j < i then (1:ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt.2 h.le]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt.2 h.le]
  linarith

/-- Deterministic non-recovery criterion: the normalised truncated graph metric is feasible
for (LP-P) and strictly beats the cut vector. -/
lemma not_recovers (V1 : Finset (Fin n)) (hn : 1 ≤ n) (hK : 1 ≤ K)
    (h1 : 8 * (∑ i, ∑ j, if i ≠ j ∧ T G K i j < K then (1:ℝ) else 0) + 4 * n ≤ (n:ℝ) ^ 2)
    (h2 : (∑ i, ∑ j, if i < j ∧ G.Adj i j then (1:ℝ) else 0)
      < K * ∑ i, ∑ j, if i < j ∧ G.Adj i j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0) :
    ¬ LPRecovers G V1 := by
  intro hrec
  set N := ∑ i, ∑ j, if i ≠ j ∧ T G K i j < K then (1:ℝ) else 0 with hN
  set E := ∑ i, ∑ j, if i < j ∧ G.Adj i j then (1:ℝ) else 0 with hE
  set E0 := ∑ i, ∑ j, if i < j ∧ G.Adj i j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0 with hE0
  set S := ∑ i, ∑ j, if i < j then (T G K i j : ℝ) else 0 with hS
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hSlow : (K:ℝ) * (((n:ℝ) ^ 2 - n) / 2 - N) ≤ S := by
    rw [← count_lt n, hN, hS, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro i _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro j _
    by_cases hij : i < j
    · have hne : i ≠ j := ne_of_lt hij
      by_cases hT : T G K i j < K
      · simp only [hij, hne, hT, if_true, ne_eq, not_false_eq_true, and_self]
        simp
      · have : (K:ℝ) ≤ T G K i j := by exact_mod_cast not_lt.1 hT
        simp only [hij, hT, if_true, if_false, and_false]
        linarith
    · simp only [hij, if_false]
      split_ifs <;> linarith
  have hS3 : 3 * K * (n:ℝ) ^ 2 ≤ 8 * S := by nlinarith
  have hSpos : 0 < S := by
    have : 0 < 3 * (K:ℝ) * (n:ℝ) ^ 2 := by positivity
    linarith
  set s : ℝ := (n:ℝ) ^ 2 / (4 * S) with hs
  have hs0 : 0 ≤ s := by positivity
  have hsK : s * (3 * K) ≤ 2 := by
    rw [hs, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  let x : Fin n → Fin n → ℝ := fun i j => s * (T G K i j : ℝ)
  have hfeas : LPFeasible n x := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i j; simp only [x]; rw [T_comm]
    · intro i; simp only [x]; rw [T_self]; simp
    · intro i j k _ _ _
      simp only [x]
      have h := T_triangle G K i j k
      rw [T_comm G K k j] at h
      have h' : (T G K i j : ℝ) ≤ T G K i k + T G K j k := by exact_mod_cast h
      nlinarith
    · intro i j k _ _
      simp only [x]
      have a1 : (T G K i j : ℝ) ≤ K := by exact_mod_cast T_le G K i j
      have a2 : (T G K i k : ℝ) ≤ K := by exact_mod_cast T_le G K i k
      have a3 : (T G K j k : ℝ) ≤ K := by exact_mod_cast T_le G K j k
      nlinarith
    · have : (∑ i, ∑ j, if i < j then x i j else 0) = s * S := by
        rw [hS, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
        simp only [x]; split_ifs <;> simp
      rw [this, hs]; field_simp
  have hobjx : lpObj G x = s * E := by
    unfold lpObj
    rw [hE, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    simp only [x]
    split_ifs with h
    · rw [T_adj G K hK h.2]; simp
    · simp
  have hobjc : lpObj G (cutVec V1) = E0 := by
    unfold lpObj
    rw [hE0]; apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    unfold cutVec
    by_cases h : i < j ∧ G.Adj i j
    · by_cases h' : sameSide V1 i j
      · simp [h, h']
      · simp [h, h']
    · have : ¬ (i < j ∧ G.Adj i j ∧ ¬ sameSide V1 i j) := fun h'' => h ⟨h''.1, h''.2.1⟩
      simp only [h, this, if_false]
  have hle := hrec.1.2 x hfeas
  rw [hobjx, hobjc] at hle
  have hE0nn : 0 ≤ E := by
    rw [hE]; apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
    split_ifs <;> norm_num
  have hE0pos : 0 < E0 := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith


lemma N_le (hK : 1 ≤ K) (D : ℝ) (hD : 1 ≤ D) (hdeg : ∀ v, (G.degree v : ℝ) ≤ D) :
    (∑ i, ∑ j, if i ≠ j ∧ T G K i j < K then (1:ℝ) else 0) ≤ n * K * D ^ K := by
  have hpt : ∀ i j, (if i ≠ j ∧ T G K i j < K then (1:ℝ) else 0)
      ≤ ∑ l ∈ Finset.range K, (G.adjMatrix ℝ ^ l) i j := by
    intro i j
    split_ifs with h
    · obtain ⟨he, _⟩ := T_lt G K h.1 h.2
      have h1 := pow_entry_ge_one G he
      have h2 : (G.adjMatrix ℝ ^ (T G K i j)) i j ≤ ∑ l ∈ Finset.range K, (G.adjMatrix ℝ ^ l) i j :=
        Finset.single_le_sum (f := fun l => (G.adjMatrix ℝ ^ l) i j)
          (fun l _ => pow_entry_nonneg G l i j) (Finset.mem_range.2 h.2)
      linarith
    · exact Finset.sum_nonneg (fun l _ => pow_entry_nonneg G l i j)
  calc (∑ i, ∑ j, if i ≠ j ∧ T G K i j < K then (1:ℝ) else 0)
      ≤ ∑ i, ∑ j, ∑ l ∈ Finset.range K, (G.adjMatrix ℝ ^ l) i j :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
    _ = ∑ l ∈ Finset.range K, ∑ i, ∑ j, (G.adjMatrix ℝ ^ l) i j := by
        rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]; exact Finset.sum_comm
    _ ≤ ∑ l ∈ Finset.range K, ∑ _i : Fin n, D ^ K := by
        apply Finset.sum_le_sum; intro l hl; apply Finset.sum_le_sum; intro i _
        have := row_sum_le G D (by linarith) hdeg l i
        have h2 : D ^ l ≤ D ^ K := pow_le_pow_right₀ hD (Finset.mem_range.1 hl).le
        linarith
    _ = n * K * D ^ K := by simp; ring

end Det

section Prob

/-- the sum over `pairs n` as an ordered double sum. -/
lemma sum_pairs {n : ℕ} (f : Fin n × Fin n → ℝ) :
    ∑ p ∈ pairs n, f p = ∑ i, ∑ j, if i < j then f (i, j) else 0 := by
  rw [pairs, Finset.sum_filter, Fintype.sum_prod_type]

lemma ind_exists_le {n : ℕ} (A : Fin n → Prop) :
    (if (∃ v, A v) then (1:ℝ) else 0) ≤ ∑ v, if A v then (1:ℝ) else 0 := by
  split_ifs with h
  · obtain ⟨v, hv⟩ := h
    have := Finset.single_le_sum (f := fun v => if A v then (1:ℝ) else 0)
      (fun v _ => by split_ifs <;> norm_num) (Finset.mem_univ v)
    simpa [hv] using this
  · exact Finset.sum_nonneg (fun v _ => by split_ifs <;> norm_num)

lemma degree_le_card {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.degree v ≤ ((pairs n).filter (fun p => G.Adj p.1 p.2 ∧ (p.1 = v ∨ p.2 = v))).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (fun u => (min u v, max u v))
  · intro u hu
    have hu' : G.Adj v u := by simpa using hu
    have hne : u ≠ v := (G.ne_of_adj hu').symm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_pairs]
    rcases lt_or_gt_of_ne hne with h | h
    · simp [min_eq_left h.le, max_eq_right h.le, h, hu'.symm]
    · simp [min_eq_right h.le, max_eq_left h.le, h, hu']
  · intro u hu w hw heq
    have hu' : G.Adj v u := by simpa using hu
    have hw' : G.Adj v w := by simpa using hw
    have hne1 : u ≠ v := (G.ne_of_adj hu').symm
    have hne2 : w ≠ v := (G.ne_of_adj hw').symm
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    rcases lt_or_gt_of_ne hne1 with a | a <;> rcases lt_or_gt_of_ne hne2 with b | b
    · rw [min_eq_left a.le, min_eq_left b.le] at h1; exact h1
    · rw [min_eq_left a.le, min_eq_right b.le] at h1; exact absurd h1 (ne_of_lt a)
    · rw [min_eq_right a.le, min_eq_left b.le] at h1; exact absurd h1.symm (ne_of_lt b)
    · rw [max_eq_left a.le, max_eq_left b.le] at h2; exact h2

lemma deg_bound {n : ℕ} (r : Fin n → Fin n → ℝ) (pmax : ℝ) (hpm : 0 ≤ pmax)
    (hr : ∀ i j, 0 ≤ r i j ∧ r i j ≤ pmax) (D : ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if (∃ v, D < (G.degree v : ℝ)) then 1 else 0)
      ≤ n * Real.exp (4 * n * pmax - D) := by
  have hstep : ∀ v : Fin n, ∑ G : SimpleGraph (Fin n),
      edgeWeight G r * (if D < (G.degree v : ℝ) then 1 else 0) ≤ Real.exp (4 * n * pmax - D) := by
    intro v
    set g : Fin n × Fin n → ℝ := fun p => if p.1 = v ∨ p.2 = v then Real.exp 1 else 1 with hg
    have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; split_ifs <;> positivity
    have hM := markov r (fun G => D < (G.degree v : ℝ))
      (fun G => ∏ p ∈ pairs n, (if G.Adj p.1 p.2 then g p else 1)) (Real.exp D) (Real.exp_pos D)
      (fun G => Finset.prod_nonneg (fun p _ => by split_ifs; exact hg0 p; norm_num))
      (by
        intro G hG
        have hY : ∏ p ∈ pairs n, (if G.Adj p.1 p.2 then g p else 1)
            = Real.exp ((((pairs n).filter (fun p => G.Adj p.1 p.2 ∧ (p.1 = v ∨ p.2 = v))).card : ℕ) : ℝ) := by
          have h1 : ∏ p ∈ pairs n, (if G.Adj p.1 p.2 then g p else 1)
              = ∏ p ∈ pairs n, (if G.Adj p.1 p.2 ∧ (p.1 = v ∨ p.2 = v) then Real.exp 1 else 1) := by
            apply Finset.prod_congr rfl; intro p _
            simp only [hg]
            by_cases ha : G.Adj p.1 p.2 <;> by_cases hb : (p.1 = v ∨ p.2 = v) <;> simp [ha, hb]
          rw [h1, ← Finset.prod_filter, Finset.prod_const, ← Real.exp_nat_mul, mul_one]
        rw [hY]
        apply Real.exp_le_exp.2
        have := degree_le_card G v
        have : (G.degree v : ℝ) ≤ (((pairs n).filter (fun p => G.Adj p.1 p.2 ∧ (p.1 = v ∨ p.2 = v))).card : ℝ) := by
          exact_mod_cast this
        linarith)
    refine hM.trans ?_
    rw [div_le_iff₀ (Real.exp_pos D), ← Real.exp_add, sub_add_cancel]
    refine (expect_prod_le r g hg0).trans (Real.exp_le_exp.2 ?_)
    have he : Real.exp 1 - 1 ≤ 2 := by have := Real.exp_one_lt_d9; linarith
    calc ∑ p ∈ pairs n, clamp01 (r p.1 p.2) * (g p - 1)
        ≤ ∑ p ∈ pairs n, 2 * pmax * ((if p.1 = v then 1 else 0) + (if p.2 = v then 1 else 0)) := by
          apply Finset.sum_le_sum; intro p _
          have c0 := clamp01_nonneg (r p.1 p.2)
          have c1 := clamp01_le (r p.1 p.2) (hr p.1 p.2).1
          have c2 := (hr p.1 p.2).2
          have he0 : 0 ≤ Real.exp 1 - 1 := by have := Real.add_one_le_exp 1; linarith
          obtain ⟨c, hc⟩ : ∃ c, clamp01 (r p.1 p.2) = c := ⟨_, rfl⟩
          rw [hc] at c0 c1 ⊢
          have c3 : c ≤ pmax := c1.trans c2
          clear c1 c2 hc
          simp only [hg]
          by_cases h1 : p.1 = v <;> by_cases h2 : p.2 = v <;> simp [h1, h2] <;> nlinarith
      _ ≤ ∑ p : Fin n × Fin n, 2 * pmax * ((if p.1 = v then 1 else 0) + (if p.2 = v then 1 else 0)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro p _ _; apply mul_nonneg (by linarith); split_ifs <;> norm_num
      _ = 4 * n * pmax := by
          rw [Fintype.sum_prod_type]
          have a : ∀ x : Fin n, ∑ y : Fin n, 2 * pmax * ((if (x, y).1 = v then (1:ℝ) else 0)
              + (if (x, y).2 = v then 1 else 0)) = 2 * pmax * (n * (if x = v then 1 else 0) + 1) := by
            intro x; rw [← Finset.mul_sum, Finset.sum_add_distrib]
            by_cases hx : x = v <;> simp [hx]
          rw [Finset.sum_congr rfl (fun x _ => a x), ← Finset.mul_sum, Finset.sum_add_distrib]
          simp; ring
  calc ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if (∃ v, D < (G.degree v : ℝ)) then 1 else 0)
      ≤ ∑ G : SimpleGraph (Fin n), ∑ v, edgeWeight G r * (if D < (G.degree v : ℝ) then 1 else 0) := by
        apply Finset.sum_le_sum; intro G _
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (ind_exists_le _) (edgeWeight_nonneg G r)
    _ = ∑ v, ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if D < (G.degree v : ℝ) then 1 else 0) :=
        Finset.sum_comm
    _ ≤ ∑ _v : Fin n, Real.exp (4 * n * pmax - D) := Finset.sum_le_sum (fun v _ => hstep v)
    _ = n * Real.exp (4 * n * pmax - D) := by simp


lemma cross_count {n : ℕ} (V1 : Finset (Fin n)) (hV : 2 * V1.card = n) :
    ∑ i, ∑ j, (if i < j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0) = (V1.card : ℝ) ^ 2 := by
  have hrow : ∀ i : Fin n, ∑ j, (if ¬ sameSide V1 i j then (1:ℝ) else 0) = V1.card := by
    intro i
    rw [Finset.sum_boole]
    by_cases hi : i ∈ V1
    · have : (Finset.univ.filter fun j => ¬ sameSide V1 i j) = V1ᶜ := by
        ext j; simp [sameSide, hi]
      rw [this, Finset.card_compl, Fintype.card_fin]; push_cast [show n - V1.card = V1.card by omega]
      rfl
    · have : (Finset.univ.filter fun j => ¬ sameSide V1 i j) = V1 := by
        ext j; simp [sameSide, hi]
      rw [this]
  have htot : ∑ i, ∑ j, (if ¬ sameSide V1 i j then (1:ℝ) else 0) = 2 * (V1.card : ℝ) ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => hrow i)]; simp
    have : (n : ℝ) = 2 * V1.card := by exact_mod_cast hV.symm
    rw [this]; ring
  have hsw : ∑ i, ∑ j, (if j < i ∧ ¬ sameSide V1 i j then (1:ℝ) else 0)
      = ∑ i, ∑ j, (if i < j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0) := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl
    intro j _; simp only [sameSide]; congr 1; apply propext; constructor <;>
      (rintro ⟨a, b⟩; exact ⟨a, fun h => b h.symm⟩)
  have hsplit : ∑ i, ∑ j, (if ¬ sameSide V1 i j then (1:ℝ) else 0)
      = ∑ i, ∑ j, (if i < j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0)
        + ∑ i, ∑ j, (if j < i ∧ ¬ sameSide V1 i j then (1:ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
    by_cases hs : sameSide V1 i j
    · simp [hs]
    · have hne : i ≠ j := fun h => hs (by subst h; simp [sameSide])
      rcases lt_or_gt_of_ne hne with h | h
      · simp [hs, h, not_lt.2 h.le]
      · simp [hs, h, not_lt.2 h.le]
  linarith

/-- edge probabilities of the SBM with planted side `V1`. -/
noncomputable def rV {n : ℕ} (V1 : Finset (Fin n)) (p q : ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if sameSide V1 i j then p else q

lemma chernoff2 {n : ℕ} (V1 : Finset (Fin n)) (hV : 2 * V1.card = n) (p q : ℝ) (hp : 0 ≤ p)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (hKl : Real.exp (-(lam * ((K:ℝ) - 1))) ≤ 1 / 2) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G (rV V1 p q) *
      (if (K : ℝ) * (∑ i, ∑ j, if i < j ∧ G.Adj i j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0)
          ≤ ∑ i, ∑ j, if i < j ∧ G.Adj i j then (1:ℝ) else 0 then 1 else 0)
      ≤ Real.exp (p * (Real.exp lam - 1) * (n:ℝ) ^ 2 - q * (V1.card : ℝ) ^ 2 / 2) := by
  set g : Fin n × Fin n → ℝ := fun e => if sameSide V1 e.1 e.2 then Real.exp lam
    else Real.exp (-(lam * ((K:ℝ) - 1))) with hg
  have hg0 : ∀ e, 0 ≤ g e := fun e => by simp only [hg]; split_ifs <;> positivity
  have hM := markov (rV V1 p q) (fun G => (K : ℝ) * (∑ i, ∑ j, if i < j ∧ G.Adj i j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0)
          ≤ ∑ i, ∑ j, if i < j ∧ G.Adj i j then (1:ℝ) else 0)
      (fun G => ∏ e ∈ pairs n, (if G.Adj e.1 e.2 then g e else 1)) 1 one_pos
      (fun G => Finset.prod_nonneg (fun e _ => by split_ifs; exact hg0 e; norm_num))
      (by
        intro G hG
        have hY : ∏ e ∈ pairs n, (if G.Adj e.1 e.2 then g e else 1)
            = Real.exp (∑ e ∈ pairs n, (if G.Adj e.1 e.2 then
                (if sameSide V1 e.1 e.2 then lam else -(lam * ((K:ℝ) - 1))) else 0)) := by
          rw [Real.exp_sum]; apply Finset.prod_congr rfl; intro e _
          simp only [hg]; split_ifs <;> simp
        rw [hY, sum_pairs]
        apply Real.one_le_exp
        have hpt : ∀ i j : Fin n, (if i < j then (if G.Adj (i, j).1 (i, j).2 then
            (if sameSide V1 (i, j).1 (i, j).2 then lam else -(lam * ((K:ℝ) - 1))) else 0) else 0)
            = lam * (if i < j ∧ G.Adj i j then (1:ℝ) else 0)
              - lam * K * (if i < j ∧ G.Adj i j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0) := by
          intro i j
          by_cases h1 : i < j <;> by_cases h2 : G.Adj i j <;> by_cases h3 : sameSide V1 i j <;>
            simp [h1, h2, h3] <;> ring
        simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
        nlinarith)
  simp only [div_one] at hM
  refine hM.trans ((expect_prod_le _ g hg0).trans (Real.exp_le_exp.2 ?_))
  rw [sum_pairs]
  have hel : 0 ≤ Real.exp lam - 1 := by have := Real.add_one_le_exp lam; linarith
  have hpt : ∀ i j : Fin n, (if i < j then clamp01 (rV V1 p q (i, j).1 (i, j).2) * (g (i, j) - 1) else 0)
      ≤ p * (Real.exp lam - 1) * (if i < j then (1:ℝ) else 0)
        - q / 2 * (if i < j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0) := by
    intro i j
    by_cases h1 : i < j
    · by_cases h3 : sameSide V1 i j
      · simp only [h1, h3, if_true, rV, hg, not_true_eq_false, and_false, if_false]
        have c1 := clamp01_le p hp
        have c0 := clamp01_nonneg p
        nlinarith
      · simp only [h1, h3, if_true, if_false, rV, hg, not_false_eq_true, and_self]
        rw [clamp01_eq q hq0 hq1]
        nlinarith
    · simp only [h1, if_false, false_and]
      simp
  calc ∑ i, ∑ j, (if i < j then clamp01 (rV V1 p q (i, j).1 (i, j).2) * (g (i, j) - 1) else 0)
      ≤ ∑ i, ∑ j, (p * (Real.exp lam - 1) * (if i < j then (1:ℝ) else 0)
        - q / 2 * (if i < j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
    _ = p * (Real.exp lam - 1) * (((n:ℝ) ^ 2 - n) / 2) - q / 2 * (V1.card : ℝ) ^ 2 := by
        simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [count_lt, cross_count V1 hV]
    _ ≤ p * (Real.exp lam - 1) * (n:ℝ) ^ 2 - q * (V1.card : ℝ) ^ 2 / 2 := by
        have : ((n:ℝ) ^ 2 - n) / 2 ≤ (n:ℝ) ^ 2 := by
          have : (0:ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
        have h0 : 0 ≤ p * (Real.exp lam - 1) := mul_nonneg hp hel
        nlinarith


lemma per_V1 {n : ℕ} (V1 : Finset (Fin n)) (hV : 2 * V1.card = n) (hn : 1 ≤ n) (p q : ℝ)
    (hp : 0 ≤ p) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hqp : q ≤ p) (K : ℕ) (hK1 : 1 ≤ K) (lam : ℝ)
    (hlam : 0 < lam) (hKl : Real.exp (-(lam * ((K:ℝ) - 1))) ≤ 1 / 2) (D : ℝ) (hD : 1 ≤ D)
    (hsize : 8 * (n:ℝ) * K * D ^ K + 4 * n ≤ (n:ℝ) ^ 2) :
    1 - (n * Real.exp (4 * n * p - D)
      + Real.exp (p * (Real.exp lam - 1) * (n:ℝ) ^ 2 - q * (V1.card : ℝ) ^ 2 / 2))
    ≤ ∑ G : SimpleGraph (Fin n), edgeWeight G (rV V1 p q) * (if ¬ LPRecovers G V1 then 1 else 0) := by
  have hr : ∀ i j, 0 ≤ rV V1 p q i j ∧ rV V1 p q i j ≤ p := by
    intro i j; simp only [rV]; split_ifs <;> constructor <;> linarith
  have hB1 := deg_bound (rV V1 p q) p hp hr D
  have hB2 := chernoff2 V1 hV p q hp hq0 hq1 K lam hlam hKl
  have hpt : ∀ G : SimpleGraph (Fin n),
      edgeWeight G (rV V1 p q) * (1 - (if (∃ v, D < (G.degree v : ℝ)) then 1 else 0)
        - (if (K : ℝ) * (∑ i, ∑ j, if i < j ∧ G.Adj i j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0)
          ≤ ∑ i, ∑ j, if i < j ∧ G.Adj i j then (1:ℝ) else 0 then 1 else 0))
      ≤ edgeWeight G (rV V1 p q) * (if ¬ LPRecovers G V1 then 1 else 0) := by
    intro G
    apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg G _)
    by_cases h1 : ∃ v, D < (G.degree v : ℝ)
    · rw [if_pos h1]; split_ifs <;> norm_num
    by_cases h2 : (K : ℝ) * (∑ i, ∑ j, if i < j ∧ G.Adj i j ∧ ¬ sameSide V1 i j then (1:ℝ) else 0)
          ≤ ∑ i, ∑ j, if i < j ∧ G.Adj i j then (1:ℝ) else 0
    · rw [if_pos h2]; split_ifs <;> norm_num
    rw [if_neg h1, if_neg h2]
    push Not at h1 h2
    have hN := N_le G K hK1 D hD h1
    have hnr : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have := not_recovers G K V1 hn hK1 (by nlinarith) h2
    rw [if_pos this]; norm_num
  have hsum := Finset.sum_le_sum (fun G (_ : G ∈ Finset.univ) => hpt G)
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_edgeWeight] at hsum
  linarith

end Prob

end LPSBMLog8Aux

open LPSBMLog8Aux LPCommunity.SBMRecovery LPCommunity.MinBisect LPCommunity.LPRecovery
  LPCommunity.SBMLog Filter Topology

lemma eventually_big (c : ℝ) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, c * Real.log (2 * m) ^ k + 4 ≤ 2 * m := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
  simp only [one_mul, add_zero] at h
  have hc : 0 < 1 / (2 * (|c| + 1)) := by positivity
  have h1 := h.eventually (gt_mem_nhds hc)
  have h2 : Tendsto (fun m : ℕ => (2 * (m:ℝ))) atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  filter_upwards [h2.eventually h1, h2.eventually (eventually_ge_atTop 8)] with m hm h8
  have hx : 0 < 2 * (m:ℝ) := by linarith
  rw [div_lt_iff₀ hx] at hm
  have hl : 0 ≤ Real.log (2 * m) ^ k := pow_nonneg (Real.log_nonneg (by linarith)) k
  have : c * Real.log (2 * m) ^ k ≤ (|c| + 1) * Real.log (2 * m) ^ k :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hl
  have h3 : (|c| + 1) * Real.log (2 * m) ^ k ≤ m := by
    have := mul_lt_mul_of_pos_left hm (by positivity : (0:ℝ) < 2 * (|c| + 1))
    field_simp at this
    nlinarith
  linarith

theorem solution (α β : ℝ) (hβ : 0 < β) (hαβ : β < α) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (logRegime α (2 * m)) (logRegime β (2 * m))
        (fun V1 G => ¬ LPCommunity.LPRecovery.LPRecovers G V1))
      Filter.atTop (nhds 1) := by
  have hα : 0 < α := hβ.trans hαβ
  set lam : ℝ := Real.log (1 + β / (16 * α)) with hlam_def
  have hb16 : 0 < β / (16 * α) := by positivity
  have hlam : 0 < lam := Real.log_pos (by linarith)
  have hel : Real.exp lam - 1 = β / (16 * α) := by
    rw [hlam_def, Real.exp_log (by linarith)]; ring
  set K : ℕ := ⌈Real.log 2 / lam⌉₊ + 1 with hK_def
  have hK1 : 1 ≤ K := by omega
  have hKl : Real.exp (-(lam * ((K:ℝ) - 1))) ≤ 1 / 2 := by
    have h1 : Real.log 2 / lam ≤ ⌈Real.log 2 / lam⌉₊ := Nat.le_ceil _
    have h2 : ((K:ℝ) - 1) = ⌈Real.log 2 / lam⌉₊ := by rw [hK_def]; push_cast; ring
    have h3 : Real.log 2 ≤ lam * ((K:ℝ) - 1) := by
      rw [h2]; rw [div_le_iff₀ hlam] at h1; linarith
    calc Real.exp (-(lam * ((K:ℝ) - 1))) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  set ε : ℕ → ℝ := fun m => 1 / (2 * (m:ℝ)) + Real.exp (-(β * m * Real.log (2 * m) / 8)) with hε_def
  have h2m : Tendsto (fun m : ℕ => (2 * (m:ℝ))) atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have hε : Tendsto ε atTop (𝓝 0) := by
    have a : Tendsto (fun m : ℕ => 1 / (2 * (m:ℝ))) atTop (𝓝 0) := by
      simp_rw [one_div]; exact tendsto_inv_atTop_zero.comp h2m
    have b : Tendsto (fun m : ℕ => β * m * Real.log (2 * m) / 8) atTop atTop := by
      have hb : Tendsto (fun m : ℕ => (β / 8) * (m:ℝ)) atTop atTop :=
        (tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
      apply tendsto_atTop_mono' atTop _ hb
      filter_upwards [eventually_ge_atTop 2] with m hm
      have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
      have hL : 1 ≤ Real.log (2 * m) := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        have := Real.exp_one_lt_d9; linarith
      have : (0:ℝ) ≤ β * m := by positivity
      nlinarith
    have c := Real.tendsto_exp_neg_atTop_nhds_zero.comp b
    have := a.add c
    rw [zero_add] at this
    exact this
  have hlow : ∀ᶠ m : ℕ in atTop, 1 - ε m ≤ sbmProb (2 * m) (logRegime α (2 * m)) (logRegime β (2 * m))
        (fun V1 G => ¬ LPRecovers G V1) ∧
      sbmProb (2 * m) (logRegime α (2 * m)) (logRegime β (2 * m))
        (fun V1 G => ¬ LPRecovers G V1) ≤ 1 := by
    filter_upwards [eventually_big (8 * K * (4 * α + 2) ^ K) K, eventually_big β 1,
      eventually_ge_atTop 2] with m h1 h2 hm2
    have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm2
    set L := Real.log (2 * (m:ℝ)) with hL_def
    have hL : 1 ≤ L := by
      rw [hL_def, Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hn : ((2 * m : ℕ) : ℝ) = 2 * (m:ℝ) := by push_cast; ring
    have hp : logRegime α (2 * m) = α * L / (2 * m) := by rw [logRegime, hn]
    have hq : logRegime β (2 * m) = β * L / (2 * m) := by rw [logRegime, hn]
    have hmpos : (0:ℝ) < 2 * m := by linarith
    -- bisections
    have hbis : ∀ V1 ∈ bisections (2 * m), 2 * V1.card = 2 * m := by
      intro V1 hV1; simpa [bisections, IsBisection] using hV1
    have hne : 0 < (bisections (2 * m)).card := by
      apply Finset.card_pos.2
      refine ⟨Finset.univ.filter (fun i : Fin (2 * m) => (i : ℕ) < m), ?_⟩
      rw [bisections, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold IsBisection
      rw [Fin.card_filter_val_lt]; omega
    have hterm : ∀ V1 ∈ bisections (2 * m), 1 - ε m ≤
        ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G
          (fun i j => if sameSide V1 i j then logRegime α (2 * m) else logRegime β (2 * m)) *
          (if ¬ LPRecovers G V1 then 1 else 0) := by
      intro V1 hV1
      have hV := hbis V1 hV1
      have hcard : (V1.card : ℝ) = m := by rw [show V1.card = m by omega]
      have hp0 : 0 ≤ logRegime α (2 * m) := by rw [hp]; positivity
      have hq0 : 0 ≤ logRegime β (2 * m) := by rw [hq]; positivity
      have hq1 : logRegime β (2 * m) ≤ 1 := by
        rw [hq, div_le_one hmpos]; simp at h2; linarith
      have hqp : logRegime β (2 * m) ≤ logRegime α (2 * m) := by
        rw [hp, hq]; apply div_le_div_of_nonneg_right _ hmpos.le; nlinarith
      set D := (4 * α + 2) * L with hD_def
      have hD : 1 ≤ D := by nlinarith
      have hsize : 8 * ((2 * m : ℕ) : ℝ) * K * D ^ K + 4 * ((2 * m : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) ^ 2 := by
        rw [hn]
        have : 8 * K * D ^ K + 4 ≤ 2 * (m:ℝ) := by
          rw [hD_def, mul_pow]; nlinarith
        nlinarith
      have key := per_V1 V1 hV (by omega) _ _ hp0 hq0 hq1 hqp K hK1 lam hlam hKl D hD hsize
      have e1 : ((2 * m : ℕ) : ℝ) * Real.exp (4 * ((2 * m : ℕ) : ℝ) * logRegime α (2 * m) - D)
          = 1 / (2 * m) := by
        rw [hn, hp]
        have : 4 * (2 * (m:ℝ)) * (α * L / (2 * m)) - D = -Real.log ((2 * (m:ℝ)) ^ 2) := by
          rw [Real.log_pow, hD_def, ← hL_def]; field_simp; ring
        rw [this, Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
      have e2 : logRegime α (2 * m) * (Real.exp lam - 1) * ((2 * m : ℕ) : ℝ) ^ 2
          - logRegime β (2 * m) * (V1.card : ℝ) ^ 2 / 2 = -(β * m * L / 8) := by
        rw [hn, hp, hq, hel, hcard]; field_simp; ring
      rw [e1, e2] at key
      exact key
    constructor
    · unfold sbmProb
      beta_reduce
      have := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at this
      have hc : (0:ℝ) < (bisections (2 * m)).card := by exact_mod_cast hne
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc, mul_comm]
      convert this using 1
      apply Finset.sum_congr rfl; intro V1 _; apply Finset.sum_congr rfl; intro G _
      congr 1; by_cases h : LPRecovers G V1 <;> simp [h]
    · unfold sbmProb
      have hc : (0:ℝ) < (bisections (2 * m)).card := by exact_mod_cast hne
      rw [one_div, ← div_eq_inv_mul, div_le_one hc]
      calc _ ≤ ∑ V1 ∈ bisections (2 * m), (1:ℝ) := by
            apply Finset.sum_le_sum; intro V1 _
            refine le_trans ?_ (le_of_eq (sum_edgeWeight (fun i j => if sameSide V1 i j then
              logRegime α (2 * m) else logRegime β (2 * m))))
            apply Finset.sum_le_sum; intro G _
            have := edgeWeight_nonneg G (fun i j => if sameSide V1 i j then logRegime α (2 * m)
              else logRegime β (2 * m))
            split_ifs <;> nlinarith
        _ = _ := by simp
  have hlim : Tendsto (fun m => 1 - ε m) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
    (hlow.mono fun m h => h.1) (hlow.mono fun m h => h.2)
