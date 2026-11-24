-- Prove2me | solution 1 for MeanBudgetXC.section_4_3_host
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T19:48:54.575138+00:00
-- url     : https://prove2.me/submissions/6152f4c3-ede8-4760-add6-a1fb758597c5

import Mathlib
import Definitions.Def_MeanBudgetXC_hostGraph
import Definitions.Def_MeanBudgetXC_isEndpoint
import Definitions.Def_MeanBudgetXC_heavyCount
import Definitions.Def_MeanBudgetXC_IsCanonical

namespace MeanBudgetXC.HostAux

open MeanBudgetXC Finset

variable {n₀ t ℓ c niso : ℕ} {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]

theorem deg_path (s : Fin 2) (i : Fin n₀) (k : Fin 4) :
    (∑ y : HostV n₀ t ℓ c niso,
      if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inl (s, i, k)) y then (1 : ℕ) else 0) =
      if k = 0 ∨ k = 3 then 2 * n₀ + 1 else 2 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]
  fin_cases s <;> fin_cases k <;>
    simp [hostGraph, hostRel, SimpleGraph.fromRel_adj, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_add_distrib] <;>
    omega

theorem hdeg_path (s : Fin 2) (i : Fin n₀) (k : Fin 4) :
    (∑ y : HostV n₀ t ℓ c niso,
      if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inl (s, i, k)) y ∧
        ¬ (isEndpoint (Sum.inl (s, i, k) : HostV n₀ t ℓ c niso) = true ∧ isEndpoint y = true)
      then (1 : ℕ) else 0) =
      if k = 0 ∨ k = 3 then 1 else 2 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]
  fin_cases s <;> fin_cases k <;>
    simp [hostGraph, hostRel, isEndpoint, SimpleGraph.fromRel_adj, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.sum_add_distrib] <;>
    omega

theorem deg_pad (p : Fin ℓ) (u : Fin t) :
    (∑ y : HostV n₀ t ℓ c niso,
      if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inl (p, u))) y then (1 : ℕ) else 0) =
      ∑ u', if T.Adj u u' then 1 else 0 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [hostGraph, hostRel, SimpleGraph.fromRel_adj]
  rw [Fintype.sum_eq_single p (fun p' hp => by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨-, h | h⟩
    · exact hp h.1.symm
    · exact hp h.1)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h | h⟩ <;> first | exact h | exact h.symm | exact h.2 | exact h.2.symm
  · intro h
    first
      | exact ⟨T.ne_of_adj h, Or.inl h⟩
      | exact ⟨fun _ => T.ne_of_adj h, Or.inl ⟨rfl, h⟩⟩
      | exact ⟨fun _ => T.ne_of_adj h, Or.inl h⟩
      | simp [h, T.ne_of_adj h]

theorem deg_mark (m : Fin c) (b : Fin 2) :
    (∑ y : HostV n₀ t ℓ c niso,
      if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inr (Sum.inl (m, b)))) y then (1 : ℕ)
      else 0) = 1 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases b <;>
    simp [hostGraph, hostRel, SimpleGraph.fromRel_adj, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.sum_add_distrib]

theorem deg_iso (w : Fin niso) :
    (∑ y : HostV n₀ t ℓ c niso,
      if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inr (Sum.inr w))) y then (1 : ℕ)
      else 0) = 0 := by
  simp [Fintype.sum_sum_type, hostGraph, hostRel, SimpleGraph.fromRel_adj]

theorem degree_eq (x : HostV n₀ t ℓ c niso) :
    (hostGraph n₀ t ℓ c niso T).degree x =
      ∑ y, if (hostGraph n₀ t ℓ c niso T).Adj x y then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter]

theorem T_degree_eq (u : Fin t) : T.degree u = ∑ u', if T.Adj u u' then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter]

/-! ### Adjacency inside each block -/

theorem three_val : ((3 : Fin 4) : ℕ) = 3 := rfl

theorem adj_ll {s s' : Fin 2} {i i' : Fin n₀} {k k' : Fin 4}
    (h : (hostGraph n₀ t ℓ c niso T).Adj (Sum.inl (s, i, k)) (Sum.inl (s', i', k'))) :
    ¬ (s.val = s'.val ∧ i.val = i'.val ∧ k.val = k'.val) ∧
      ((s.val = s'.val ∧ i.val = i'.val ∧ k.val + 1 = k'.val) ∨
        (s.val = s'.val ∧ i.val = i'.val ∧ k'.val + 1 = k.val) ∨
        (s.val = 0 ∧ s'.val = 1 ∧ (k.val = 0 ∨ k.val = 3) ∧ (k'.val = 0 ∨ k'.val = 3)) ∨
        (s'.val = 0 ∧ s.val = 1 ∧ (k'.val = 0 ∨ k'.val = 3) ∧ (k.val = 0 ∨ k.val = 3))) := by
  rw [hostGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨hne, h⟩ := h
  refine ⟨fun ⟨h1, h2, h3⟩ => hne (by
    rw [Fin.ext_iff.mpr h1, Fin.ext_iff.mpr h2, Fin.ext_iff.mpr h3]), ?_⟩
  rcases h with h | h
  · have h' := of_decide_eq_true (h : decide ((s = s' ∧ i = i' ∧ k.val + 1 = k'.val) ∨
        (s = 0 ∧ s' = 1 ∧ (k = 0 ∨ k = 3) ∧ (k' = 0 ∨ k' = 3))) = true)
    simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, three_val] at h'
    omega
  · have h' := of_decide_eq_true (h : decide ((s' = s ∧ i' = i ∧ k'.val + 1 = k.val) ∨
        (s' = 0 ∧ s = 1 ∧ (k' = 0 ∨ k' = 3) ∧ (k = 0 ∨ k = 3))) = true)
    simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, three_val] at h'
    omega

theorem adj_pp {p p' : Fin ℓ} {u u' : Fin t}
    (h : (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inl (p, u))) (Sum.inr (Sum.inl (p', u')))) :
    T.Adj u u' := by
  rw [hostGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact (of_decide_eq_true (h : decide (p = p' ∧ T.Adj u u') = true)).2
  · exact (of_decide_eq_true (h : decide (p' = p ∧ T.Adj u' u) = true)).2.symm

theorem adj_mm {m m' : Fin c} {b b' : Fin 2}
    (h : (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inr (Sum.inl (m, b))))
      (Sum.inr (Sum.inr (Sum.inl (m', b'))))) : b.val ≠ b'.val := by
  rw [hostGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · have h' := of_decide_eq_true (h : decide (m = m' ∧ b = 0 ∧ b' = 1) = true)
    rw [h'.2.1, h'.2.2]; decide
  · have h' := of_decide_eq_true (h : decide (m' = m ∧ b' = 0 ∧ b = 1) = true)
    rw [h'.2.1, h'.2.2]; decide

/-- The block of a host vertex. -/
def blk : HostV n₀ t ℓ c niso → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

theorem adj_blk {x y : HostV n₀ t ℓ c niso} (h : (hostGraph n₀ t ℓ c niso T).Adj x y) :
    blk x = blk y := by
  rcases x with _ | _ | _ | _ <;> rcases y with _ | _ | _ | _ <;>
    first
      | rfl
      | (exfalso; revert h; simp [hostGraph, hostRel, SimpleGraph.fromRel_adj])

theorem not_adj_iso {w : Fin niso} {y : HostV n₀ t ℓ c niso} :
    ¬ (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inr (Sum.inr w))) y := by
  rcases y with _ | _ | _ | _ <;> simp [hostGraph, hostRel, SimpleGraph.fromRel_adj]

set_option maxHeartbeats 1000000 in
theorem cliqueFree (htri : T.CliqueFree 3) : (hostGraph n₀ t ℓ c niso T).CliqueFree 3 := by
  intro S hS
  rw [SimpleGraph.is3Clique_iff] at hS
  obtain ⟨a, b, d, hab, had, hbd, -⟩ := hS
  have e1 := adj_blk hab
  have e2 := adj_blk had
  rcases a with ⟨s1, i1, k1⟩ | ⟨p1, u1⟩ | ⟨m1, b1⟩ | w1 <;>
  rcases b with ⟨s2, i2, k2⟩ | ⟨p2, u2⟩ | ⟨m2, b2⟩ | w2 <;>
  rcases d with ⟨s3, i3, k3⟩ | ⟨p3, u3⟩ | ⟨m3, b3⟩ | w3 <;>
  simp only [blk] at e1 e2 <;>
  first
    | omega
    | exact not_adj_iso hab
    | (have h1 := adj_ll hab; have h2 := adj_ll had; have h3 := adj_ll hbd
       have := s1.isLt; have := s2.isLt; have := s3.isLt
       have := k1.isLt; have := k2.isLt; have := k3.isLt
       omega)
    | (exact htri {u1, u2, u3}
        (SimpleGraph.is3Clique_triple_iff.mpr ⟨adj_pp hab, adj_pp had, adj_pp hbd⟩))
    | (have h1 := adj_mm hab; have h2 := adj_mm had; have h3 := adj_mm hbd
       have := b1.isLt; have := b2.isLt; have := b3.isLt
       omega)

/-! ### Counting edges through ordered adjacent pairs -/

theorem sum_adj_filter {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Sym2 V → Prop) [DecidablePred P] :
    ∑ x, ∑ y, (if G.Adj x y ∧ P s(x, y) then 1 else 0 : ℕ) = 2 * (G.edgeFinset.filter P).card := by
  classical
  let g : Sym2 V → ℕ := fun z => if z ∈ G.edgeSet ∧ P z then 1 else 0
  have h1 : ∀ x y, (if G.Adj x y ∧ P s(x, y) then 1 else 0 : ℕ) = g s(x, y) := by
    intro x y
    simp only [g, SimpleGraph.mem_edgeSet]
  have h2 : ∑ x, ∑ y, (if G.Adj x y ∧ P s(x, y) then 1 else 0 : ℕ) =
      ∑ p : V × V, g s(p.1, p.2) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [h1]
  have h3 : ∑ p : V × V, g s(p.1, p.2) = ∑ z : Sym2 V, 2 * g z := by
    rw [← Finset.sum_fiberwise Finset.univ (fun p : V × V => s(p.1, p.2))
      (fun p => g s(p.1, p.2))]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
      Finset.sum_const, smul_eq_mul]
    induction z using Sym2.ind with
    | h a b =>
      by_cases hab : a = b
      · subst hab
        have : g s(a, a) = 0 := by simp [g]
        rw [this]; simp
      · have hf : (Finset.univ.filter (fun p : V × V => s(p.1, p.2) = s(a, b))) =
            {(a, b), (b, a)} := by
          ext ⟨u, v⟩
          simp [Sym2.eq_iff]
        rw [hf, Finset.card_pair (fun h => hab (congrArg Prod.fst h))]
  have h4 : ∑ z : Sym2 V, g z = (G.edgeFinset.filter P).card := by
    rw [Finset.card_filter]
    rw [← Finset.sum_subset (Finset.subset_univ G.edgeFinset) (fun z _ hz => by
      simp only [g]; rw [if_neg]; rintro ⟨h, -⟩; exact hz (SimpleGraph.mem_edgeFinset.mpr h))]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    simp only [g, SimpleGraph.mem_edgeFinset.mp hz, true_and]
  rw [h2, h3, ← Finset.mul_sum, h4]

end MeanBudgetXC.HostAux

open MeanBudgetXC MeanBudgetXC.HostAux Finset in
theorem solution (n₀ t ℓ c niso : ℕ) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] :
    Fintype.card (HostV n₀ t ℓ c niso) = 8 * n₀ + t * ℓ + 2 * c + niso ∧
      (T.CliqueFree 3 → (hostGraph n₀ t ℓ c niso T).CliqueFree 3) ∧
      (1 ≤ n₀ → 1 ≤ ℓ →
        (hostGraph n₀ t ℓ c niso T).maxDegree = max (max (2 * n₀ + 1) T.maxDegree) 2) ∧
      ((hostGraph n₀ t ℓ c niso T).edgeFinset.filter
          (fun e => ¬ ∀ x ∈ e.toFinset, isEndpoint x = true)).card = heavyCount n₀ ℓ c T ∧
      (hostGraph n₀ t ℓ c niso T).edgeFinset.card = 4 * n₀ ^ 2 + heavyCount n₀ ℓ c T ∧
      ∀ S : Finset (HostV n₀ t ℓ c niso), IsCanonical T S →
        S.card = 4 * n₀ + T.vertexCoverNum.toNat * ℓ + c := by
  have hTsum : ∑ u : Fin t, T.degree u = 2 * T.edgeFinset.card := T.sum_degrees_eq_twice_card_edges
  have hpad : ∀ p : Fin ℓ, ∀ u : Fin t, (hostGraph n₀ t ℓ c niso T).degree
      (Sum.inr (Sum.inl (p, u))) = T.degree u := by
    intro p u; rw [degree_eq, deg_pad, ← T_degree_eq]
  refine ⟨?_, cliqueFree, ?_, ?_, ?_, ?_⟩
  · simp [Fintype.card_sum, Fintype.card_prod]; ring
  · -- maximum degree
    intro hn hl
    apply le_antisymm
    · apply SimpleGraph.maxDegree_le_of_forall_degree_le
      intro v
      rcases v with ⟨s, i, k⟩ | ⟨p, u⟩ | ⟨m, b⟩ | w
      · rw [degree_eq, deg_path]
        split_ifs
        · exact le_max_of_le_left (le_max_left _ _)
        · exact le_max_right _ _
      · rw [hpad]
        exact (T.degree_le_maxDegree u).trans (le_max_of_le_left (le_max_right _ _))
      · rw [degree_eq, deg_mark]
        exact (by norm_num : 1 ≤ 2).trans (le_max_right _ _)
      · rw [degree_eq, deg_iso]; exact Nat.zero_le _
    · have h1 : 2 * n₀ + 1 ≤ (hostGraph n₀ t ℓ c niso T).maxDegree := by
        have := (hostGraph n₀ t ℓ c niso T).degree_le_maxDegree
          (Sum.inl ((0 : Fin 2), (⟨0, hn⟩ : Fin n₀), (0 : Fin 4)))
        rw [degree_eq, deg_path, if_pos (Or.inl rfl)] at this
        exact this
      have h2 : T.maxDegree ≤ (hostGraph n₀ t ℓ c niso T).maxDegree := by
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht
          have : T.maxDegree ≤ 0 :=
            T.maxDegree_le_of_forall_degree_le 0 (fun u => u.elim0)
          omega
        · have : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
          obtain ⟨u, hu⟩ := T.exists_maximal_degree_vertex
          have := (hostGraph n₀ t ℓ c niso T).degree_le_maxDegree
            (Sum.inr (Sum.inl ((⟨0, hl⟩ : Fin ℓ), u)))
          rw [hpad, ← hu] at this
          exact this
      exact max_le (max_le h1 h2) (by omega)
  · -- heavy edges
    have key := sum_adj_filter (hostGraph n₀ t ℓ c niso T)
      (fun e => ¬ ∀ x ∈ e.toFinset, isEndpoint x = true)
    have hcond : ∀ x y : HostV n₀ t ℓ c niso,
        (if (hostGraph n₀ t ℓ c niso T).Adj x y ∧
          ¬ ∀ z ∈ (s(x, y) : Sym2 _).toFinset, isEndpoint z = true then (1 : ℕ) else 0) =
        if (hostGraph n₀ t ℓ c niso T).Adj x y ∧
          ¬ (isEndpoint x = true ∧ isEndpoint y = true) then 1 else 0 := by
      intro x y
      apply if_congr _ rfl rfl
      simp [Sym2.toFinset_mk_eq]
    simp only [hcond] at key
    have hsum : ∑ x : HostV n₀ t ℓ c niso, ∑ y : HostV n₀ t ℓ c niso,
        (if (hostGraph n₀ t ℓ c niso T).Adj x y ∧
          ¬ (isEndpoint x = true ∧ isEndpoint y = true) then (1 : ℕ) else 0) =
        2 * heavyCount n₀ ℓ c T := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
      have e1 : ∑ x : Fin 2 × Fin n₀ × Fin 4, ∑ y : HostV n₀ t ℓ c niso,
          (if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inl x) y ∧
            ¬ (isEndpoint (Sum.inl x : HostV n₀ t ℓ c niso) = true ∧ isEndpoint y = true)
          then (1 : ℕ) else 0) = 12 * n₀ := by
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_prod_type, hdeg_path, Fin.sum_univ_two, Fin.sum_univ_four]
        simp
        ring
      have e2 : ∑ x : Fin ℓ × Fin t, ∑ y : HostV n₀ t ℓ c niso,
          (if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inl x)) y ∧
            ¬ (isEndpoint (Sum.inr (Sum.inl x) : HostV n₀ t ℓ c niso) = true ∧
              isEndpoint y = true) then (1 : ℕ) else 0) = ℓ * (2 * T.edgeFinset.card) := by
        have : ∀ x : Fin ℓ × Fin t, ∑ y : HostV n₀ t ℓ c niso,
            (if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inl x)) y ∧
              ¬ (isEndpoint (Sum.inr (Sum.inl x) : HostV n₀ t ℓ c niso) = true ∧
                isEndpoint y = true) then (1 : ℕ) else 0) = T.degree x.2 := by
          intro x
          rw [← hpad x.1 x.2, degree_eq]
          exact Finset.sum_congr rfl (fun y _ => if_congr (by simp [isEndpoint]) rfl rfl)
        rw [Finset.sum_congr rfl (fun x _ => this x), Fintype.sum_prod_type]
        simp only [hTsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have e3 : ∑ x : Fin c × Fin 2, ∑ y : HostV n₀ t ℓ c niso,
          (if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inr (Sum.inl x))) y ∧
            ¬ (isEndpoint (Sum.inr (Sum.inr (Sum.inl x)) : HostV n₀ t ℓ c niso) = true ∧
              isEndpoint y = true) then (1 : ℕ) else 0) = 2 * c := by
        have : ∀ x : Fin c × Fin 2, ∑ y : HostV n₀ t ℓ c niso,
            (if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inr (Sum.inl x))) y ∧
              ¬ (isEndpoint (Sum.inr (Sum.inr (Sum.inl x)) : HostV n₀ t ℓ c niso) = true ∧
                isEndpoint y = true) then (1 : ℕ) else 0) = 1 := by
          rintro ⟨m, b⟩
          exact (Finset.sum_congr rfl (fun y _ => if_congr (by simp [isEndpoint]) rfl rfl)).trans
            (deg_mark (T := T) m b)
        rw [Finset.sum_congr rfl (fun x _ => this x)]
        simp; ring
      have e4 : ∑ x : Fin niso, ∑ y : HostV n₀ t ℓ c niso,
          (if (hostGraph n₀ t ℓ c niso T).Adj (Sum.inr (Sum.inr (Sum.inr x))) y ∧
            ¬ (isEndpoint (Sum.inr (Sum.inr (Sum.inr x)) : HostV n₀ t ℓ c niso) = true ∧
              isEndpoint y = true) then (1 : ℕ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        exact (Finset.sum_congr rfl (fun y _ => if_congr (by simp [isEndpoint]) rfl rfl)).trans
          (deg_iso (T := T) x)
      rw [e1, e2, e3, e4]
      unfold heavyCount
      ring
    rw [hsum] at key
    omega
  · -- all edges
    have key := (hostGraph n₀ t ℓ c niso T).sum_degrees_eq_twice_card_edges
    have hsum : ∑ x : HostV n₀ t ℓ c niso, (hostGraph n₀ t ℓ c niso T).degree x =
        2 * (4 * n₀ ^ 2 + heavyCount n₀ ℓ c T) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
      have e1 : ∑ x : Fin 2 × Fin n₀ × Fin 4, (hostGraph n₀ t ℓ c niso T).degree (Sum.inl x) =
          8 * n₀ ^ 2 + 12 * n₀ := by
        simp only [degree_eq, Fintype.sum_prod_type, deg_path, Fin.sum_univ_two,
          Fin.sum_univ_four]
        simp
        ring
      have e2 : ∑ x : Fin ℓ × Fin t, (hostGraph n₀ t ℓ c niso T).degree (Sum.inr (Sum.inl x)) =
          ℓ * (2 * T.edgeFinset.card) := by
        rw [Fintype.sum_prod_type]
        simp only [hpad, hTsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have e3 : ∑ x : Fin c × Fin 2,
          (hostGraph n₀ t ℓ c niso T).degree (Sum.inr (Sum.inr (Sum.inl x))) = 2 * c := by
        simp only [degree_eq, deg_mark]
        simp; ring
      have e4 : ∑ x : Fin niso,
          (hostGraph n₀ t ℓ c niso T).degree (Sum.inr (Sum.inr (Sum.inr x))) = 0 := by
        simp only [degree_eq, deg_iso, Finset.sum_const_zero]
      rw [e1, e2, e3, e4]
      unfold heavyCount
      ring
    rw [hsum] at key
    omega
  · -- canonical choices
    intro S ⟨β, C, γ, hC, hS⟩
    classical
    have hSf : S = Finset.univ.filter (fun x => canonMem β C γ x) := by
      ext x; simp [hS]
    have hCc : ∀ p, (C p).card = T.vertexCoverNum.toNat := by
      intro p; rw [← (hC p).2, ENat.toNat_natCast]
    rw [hSf, Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type,
      Fintype.sum_sum_type]
    have e1 : ∑ x : Fin 2 × Fin n₀ × Fin 4,
        (if canonMem β C γ (Sum.inl x : HostV n₀ t ℓ c niso) then 1 else 0) = 4 * n₀ := by
      have : ∀ s : Fin 2, ∀ i : Fin n₀, ∑ k : Fin 4,
          (if canonMem β C γ (Sum.inl (s, i, k) : HostV n₀ t ℓ c niso) then 1 else 0) = 2 := by
        intro s i
        rw [Fin.sum_univ_four]
        cases h : β (s, i) <;> simp [canonMem, h]
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_prod_type, this]
      simp; ring
    have e2 : ∑ x : Fin ℓ × Fin t,
        (if canonMem β C γ (Sum.inr (Sum.inl x) : HostV n₀ t ℓ c niso) then 1 else 0) =
        T.vertexCoverNum.toNat * ℓ := by
      rw [Fintype.sum_prod_type]
      have : ∀ p : Fin ℓ, ∑ u : Fin t,
          (if canonMem β C γ (Sum.inr (Sum.inl (p, u)) : HostV n₀ t ℓ c niso) then 1 else 0) =
          T.vertexCoverNum.toNat := by
        intro p
        rw [← hCc p]
        have hc : ∀ u : Fin t,
            (if canonMem β C γ (Sum.inr (Sum.inl (p, u)) : HostV n₀ t ℓ c niso) then 1 else 0) =
              (if u ∈ C p then 1 else 0) := fun u => if_congr Iff.rfl rfl rfl
        rw [Finset.sum_congr rfl (fun u _ => hc u)]
        rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
        congr 1
        ext u
        simp
      simp only [this]
      simp; ring
    have e3 : ∑ x : Fin c × Fin 2,
        (if canonMem β C γ (Sum.inr (Sum.inr (Sum.inl x)) : HostV n₀ t ℓ c niso) then 1 else 0)
        = c := by
      rw [Fintype.sum_prod_type]
      have h1 : ∀ m : Fin c, ∑ b : Fin 2,
          (if canonMem β C γ (Sum.inr (Sum.inr (Sum.inl (m, b))) : HostV n₀ t ℓ c niso)
            then 1 else 0) = 1 := by
        intro m
        simp only [canonMem]
        rw [Fin.sum_univ_two]
        have key : ∀ g : Fin 2, g = 0 ∨ g = 1 := by decide
        rcases key (γ m) with hg | hg <;> simp [hg]
      simp only [h1]
      simp
    have e4 : ∑ x : Fin niso,
        (if canonMem β C γ (Sum.inr (Sum.inr (Sum.inr x)) : HostV n₀ t ℓ c niso) then 1 else 0)
        = 0 := by
      simp [canonMem]
    rw [e1, e2, e3, e4]
    ring
