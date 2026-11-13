-- Prove2me | solution 1 for MultipleUnicast.Counterexample.flow_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:33:38.668314+00:00
-- url     : https://prove2.me/submissions/0e4018c1-6830-4988-9aa0-0ebca03dfa27

import Theorems.Thm_MultipleUnicast_Counterexample_terminal_distance
import Theorems.Thm_MultipleUnicast_Counterexample_coding_rate
import Theorems.Thm_MultipleUnicast_Counterexample_balanced_orientation

section
set_option autoImplicit false
set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample.Dev.Flow
open GeometryOfGraphs.FlowCut

section General

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Potential identity: the conservation law paired with a potential `φ`. -/
theorem potential_identity (N : Network V) (f : Fin N.k → V → V → ℝ) (r : ℝ)
    (hf : N.IsFeasibleFlow f r) (μ : Fin N.k) (φ : V → ℝ) :
    ∑ i, ∑ j, f μ i j * (φ j - φ i) = r * N.D μ * (φ (N.t μ) - φ (N.s μ)) := by
  have hcons := hf.2.1 μ
  have h1 : ∑ v, φ v * (∑ j, f μ v j - ∑ j, f μ j v) =
      ∑ v, φ v * (r * N.D μ * ((if v = N.s μ then 1 else 0) - (if v = N.t μ then 1 else 0))) :=
    Finset.sum_congr rfl fun v _ => by rw [hcons v]
  have h2 : ∑ v, φ v * (r * N.D μ * ((if v = N.s μ then 1 else 0) -
      (if v = N.t μ then 1 else 0))) = r * N.D μ * (φ (N.s μ) - φ (N.t μ)) := by
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have h3 : ∑ v, φ v * (∑ j, f μ v j - ∑ j, f μ j v) =
      ∑ i, ∑ j, f μ i j * φ i - ∑ i, ∑ j, f μ i j * φ j := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h4 : ∑ i, ∑ j, f μ i j * (φ j - φ i) =
      ∑ i, ∑ j, f μ i j * φ j - ∑ i, ∑ j, f μ i j * φ i := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h4]
  linarith [h1, h2, h3]

/-- A feasible flow vanishes on zero-capacity pairs. -/
theorem flow_eq_zero_of_cap (N : Network V) (f : Fin N.k → V → V → ℝ) (r : ℝ)
    (hf : N.IsFeasibleFlow f r) (μ : Fin N.k) (i j : V) (hC : N.C i j = 0) :
    f μ i j = 0 := by
  have hcap := hf.2.2 i j
  have hle : f μ i j + f μ j i ≤ ∑ ν, (f ν i j + f ν j i) :=
    Finset.single_le_sum (f := fun ν => f ν i j + f ν j i)
      (fun ν _ => add_nonneg (hf.1 ν i j) (hf.1 ν j i)) (Finset.mem_univ μ)
  linarith [hf.1 μ i j, hf.1 μ j i]

/-- The total load of a feasible flow is at most half the total (ordered) capacity. -/
theorem total_load_le (N : Network V) (f : Fin N.k → V → V → ℝ) (r : ℝ)
    (hf : N.IsFeasibleFlow f r) :
    2 * ∑ μ, ∑ i, ∑ j, f μ i j ≤ ∑ i, ∑ j, N.C i j := by
  have h : ∑ i, ∑ j, ∑ μ, (f μ i j + f μ j i) ≤ ∑ i, ∑ j, N.C i j :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hf.2.2 i j
  have e1 : ∑ i, ∑ j, ∑ μ, (f μ i j + f μ j i) =
      ∑ i, ∑ j, ∑ μ, f μ i j + ∑ i, ∑ j, ∑ μ, f μ j i := by
    simp only [Finset.sum_add_distrib]
  have e2 : ∑ i, ∑ j, ∑ μ, f μ j i = ∑ i, ∑ j, ∑ μ, f μ i j := Finset.sum_comm
  have e3 : ∑ μ, ∑ i, ∑ j, f μ i j = ∑ i, ∑ j, ∑ μ, f μ i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  linarith

/-- Lower bound on the load of each commodity from a 1-Lipschitz potential. -/
theorem commodity_load_ge (N : Network V) (f : Fin N.k → V → V → ℝ) (r : ℝ)
    (hf : N.IsFeasibleFlow f r) (μ : Fin N.k) (φ : V → ℝ)
    (hφ : ∀ i j, N.C i j ≠ 0 → φ j - φ i ≤ 1) :
    r * N.D μ * (φ (N.t μ) - φ (N.s μ)) ≤ ∑ i, ∑ j, f μ i j := by
  rw [← potential_identity N f r hf μ φ]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hC : N.C i j = 0
  · rw [flow_eq_zero_of_cap N f r hf μ i j hC]; simp
  · have := hφ i j hC
    have h0 := hf.1 μ i j
    nlinarith

/-- Ordered dart pairs of a walk. -/
def pairs {G : SimpleGraph V} {u v : V} (w : G.Walk u v) : List (V × V) :=
  w.darts.map SimpleGraph.Dart.toProd

/-- Conservation for dart counts of any walk. -/
theorem walk_conservation {G : SimpleGraph V} {u v : V} (w : G.Walk u v) (x : V) :
    (∑ j, ((pairs w).count (x, j) : ℝ)) - ∑ j, ((pairs w).count (j, x) : ℝ) =
      (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  induction w with
  | nil => simp [pairs]
  | @cons a b c h p ih =>
    have hp : pairs (SimpleGraph.Walk.cons h p) = (a, b) :: pairs p := by
      simp [pairs]
    rw [hp]
    simp only [List.count_cons, Nat.cast_add, Finset.sum_add_distrib, beq_iff_eq,
      Prod.mk.injEq]
    have e1 : ∑ j : V, (((if a = x ∧ b = j then 1 else 0 : ℕ)) : ℝ) =
        if x = a then 1 else 0 := by
      by_cases hx : x = a
      · subst hx; simp
      · simp [Ne.symm hx, hx]
    have e2 : ∑ j : V, (((if a = j ∧ b = x then 1 else 0 : ℕ)) : ℝ) =
        if x = b then 1 else 0 := by
      by_cases hx : x = b
      · subst hx; simp
      · simp [Ne.symm hx, hx]
    rw [e1, e2]
    linarith [ih]

omit [Fintype V] in
theorem count_pairs_eq_zero {G : SimpleGraph V} {u v : V} (w : G.Walk u v) (i j : V)
    (h : ¬ G.Adj i j) : (pairs w).count (i, j) = 0 := by
  apply List.count_eq_zero.mpr
  intro hm
  simp only [pairs, List.mem_map] at hm
  obtain ⟨d, _, hd⟩ := hm
  apply h
  have := d.adj
  rw [hd] at this
  exact this

theorem count_pairs_le {G : SimpleGraph V} {u v : V} (w : G.Walk u v) (hw : w.IsPath)
    (x : V × V) : (pairs w).count x ≤ Fintype.card V := by
  have h1 := List.count_le_length (a := x) (l := pairs w)
  have h2 : (pairs w).length = w.length := by simp [pairs]
  have h3 := hw.length_lt
  omega

/-- Path-routing witness: positive feasible rate when every source reaches its sink. -/
theorem exists_pos_flow (N : Network V) (G : SimpleGraph V)
    (hC : ∀ i j, G.Adj i j → 1 ≤ N.C i j) (hD : ∀ μ, N.D μ = 1)
    (hreach : ∀ μ, G.Reachable (N.s μ) (N.t μ)) :
    ∃ r : ℝ, 0 < r ∧ ∃ f, N.IsFeasibleFlow f r := by
  classical
  have hw : ∀ μ, ∃ w : G.Walk (N.s μ) (N.t μ), w.IsPath := fun μ => by
    obtain ⟨w⟩ := hreach μ
    exact ⟨w.toPath.1, w.toPath.2⟩
  choose w hwp using hw
  set K : ℝ := 2 * N.k * Fintype.card V + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨1 / K, by positivity, fun μ i j => (1 / K) * ((pairs (w μ)).count (i, j) : ℝ),
    ?_, ?_, ?_⟩
  · intro μ i j; positivity
  · intro μ x
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, walk_conservation, hD]
    ring
  · intro i j
    by_cases hadj : G.Adj i j
    · refine le_trans ?_ (hC i j hadj)
      have hb : ∀ μ, (1 / K) * ((pairs (w μ)).count (i, j) : ℝ) +
          (1 / K) * ((pairs (w μ)).count (j, i) : ℝ) ≤ (1 / K) * (2 * Fintype.card V) := by
        intro μ
        have a1 : ((pairs (w μ)).count (i, j) : ℝ) ≤ Fintype.card V := by
          exact_mod_cast count_pairs_le (w μ) (hwp μ) (i, j)
        have a2 : ((pairs (w μ)).count (j, i) : ℝ) ≤ Fintype.card V := by
          exact_mod_cast count_pairs_le (w μ) (hwp μ) (j, i)
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      refine le_trans (Finset.sum_le_sum fun μ _ => hb μ) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show (N.k : ℝ) * (1 / K * (2 * Fintype.card V)) = (2 * N.k * Fintype.card V) / K by
        field_simp]
      rw [div_le_one hKpos]
      linarith
    · have : ∀ μ, (1 / K) * ((pairs (w μ)).count (i, j) : ℝ) +
          (1 / K) * ((pairs (w μ)).count (j, i) : ℝ) = 0 := by
        intro μ
        rw [count_pairs_eq_zero _ i j hadj,
          count_pairs_eq_zero _ j i (fun h => hadj h.symm)]
        simp
      simp only [this, Finset.sum_const_zero]
      exact N.C_nonneg i j

/-- The truncated distance potential: `min (dist s v) L` on the component of `s`, else `L`. -/
noncomputable def pot (G : SimpleGraph V) (s : V) (L : ℕ) (v : V) : ℝ :=
  open scoped Classical in
  if G.Reachable s v then ((min (G.dist s v) L : ℕ) : ℝ) else (L : ℝ)

theorem pot_lipschitz (G : SimpleGraph V) (s : V) (L : ℕ) (i j : V) (h : G.Adj i j) :
    pot G s L j - pot G s L i ≤ 1 := by
  classical
  unfold pot
  by_cases hi : G.Reachable s i
  · have hj : G.Reachable s j := hi.trans h.reachable
    rw [if_pos hi, if_pos hj]
    have h1 : G.dist s j ≤ G.dist s i + G.dist i j := h.reachable.dist_triangle_right s
    have h2 : G.dist i j = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
    have : min (G.dist s j) L ≤ min (G.dist s i) L + 1 := by omega
    have : ((min (G.dist s j) L : ℕ) : ℝ) ≤ ((min (G.dist s i) L : ℕ) : ℝ) + 1 := by
      exact_mod_cast this
    linarith
  · have hj : ¬ G.Reachable s j := fun hj => hi (hj.trans h.symm.reachable)
    rw [if_neg hi, if_neg hj]
    norm_num

theorem pot_self (G : SimpleGraph V) (s : V) (L : ℕ) : pot G s L s = 0 := by
  classical
  unfold pot
  rw [if_pos (SimpleGraph.Reachable.refl s)]
  simp

theorem pot_far (G : SimpleGraph V) (s t : V) (L : ℕ) (hr : G.Reachable s t)
    (hd : L ≤ G.dist s t) : pot G s L t = L := by
  classical
  unfold pot
  rw [if_pos hr, min_eq_right hd]

omit [DecidableEq V] in
/-- Sum of a 0/1 adjacency capacity matrix: twice the number of edges. -/
theorem sum_adj_capacity (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ i, ∑ j, (if G.Adj i j then (1 : ℝ) else 0) = 2 * (G.edgeFinset.card : ℝ) := by
  have h : ∀ i, ∑ j, (if G.Adj i j then (1 : ℝ) else 0) = (G.degree i : ℝ) := by
    intro i
    rw [Finset.sum_boole, ← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_eq_filter]
  simp only [h]
  rw [← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges]
  push_cast; ring

end General

section Specific
open MultipleUnicast.Counterexample
open scoped Classical

theorem pointEnd_lt (q : Edge) : (pointEnd q).val < 91 := (edgePair q).1.isLt

theorem lineEnd_ge (q : Edge) : 91 ≤ (lineEnd q).val := by
  simp [lineEnd]

theorem ends_inj {q q' : Edge} (hp : pointEnd q = pointEnd q') (hl : lineEnd q = lineEnd q') :
    q = q' := by
  apply (balanced_orientation.2.2.1)
  have hp' := congrArg Fin.val hp
  have hl' := congrArg Fin.val hl
  simp only [pointEnd, lineEnd] at hp' hl'
  exact Prod.ext (Fin.ext hp') (Fin.ext (by omega))

theorem edgeFinset_eq [Fintype graph.edgeSet] :
    graph.edgeFinset = physical.image (fun q => s(pointEnd q, lineEnd q)) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image]
    constructor
    · rintro ⟨q, hq, h⟩
      refine ⟨q, hq, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, Sym2.eq_swap]
    · rintro ⟨q, hq, h⟩
      refine ⟨q, hq, ?_⟩
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩

theorem edgeFinset_card [Fintype graph.edgeSet] : graph.edgeFinset.card = 735 := by
  rw [edgeFinset_eq, Finset.card_image_of_injOn, balanced_orientation.2.2.2.2.2.2.2.2.2.2.2.1]
  intro q _ q' _ h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ends_inj h1 h2
  · have a := congrArg Fin.val h1
    have := pointEnd_lt q
    have := lineEnd_ge q'
    omega

theorem total_capacity : ∑ i, ∑ j, network.C i j = 1470 := by
  classical
  have h : ∀ i j, network.C i j = if graph.Adj i j then (1 : ℝ) else 0 := by
    intro i j
    show (if graph.Adj i j then (1 : ℝ) else 0) = _
    congr 1
  simp only [h]
  rw [sum_adj_capacity, edgeFinset_card]
  norm_num

theorem adj_of_cap (i j : Vertex) (h : network.C i j ≠ 0) : graph.Adj i j := by
  by_contra hn
  apply h
  show (if graph.Adj i j then (1 : ℝ) else 0) = 0
  rw [if_neg hn]

theorem cap_of_adj (i j : Vertex) (h : graph.Adj i j) : 1 ≤ network.C i j := by
  show 1 ≤ (if graph.Adj i j then (1 : ℝ) else 0)
  rw [if_pos h]

theorem k_eq : network.k = 157 := coding_rate.1

theorem rate_le (r : ℝ) (f : Fin network.k → Vertex → Vertex → ℝ)
    (hf : network.IsFeasibleFlow f r) : r ≤ (147 : ℝ) / 157 := by
  have hload : ∀ μ, r * 5 ≤ ∑ i, ∑ j, f μ i j := by
    intro μ
    have := commodity_load_ge network f r hf μ (pot graph (network.s μ) 5)
      (fun i j h => pot_lipschitz graph _ 5 i j (adj_of_cap i j h))
    obtain ⟨hr, hd⟩ := terminal_distance μ
    rw [pot_far graph _ _ 5 hr hd, pot_self] at this
    have hD : network.D μ = 1 := rfl
    rw [hD] at this
    push_cast at this
    linarith
  have htot := total_load_le network f r hf
  rw [total_capacity] at htot
  have hsum : ∑ μ : Fin network.k, r * 5 ≤ ∑ μ, ∑ i, ∑ j, f μ i j :=
    Finset.sum_le_sum fun μ _ => hload μ
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hk : (network.k : ℝ) = 157 := by exact_mod_cast k_eq
  rw [hk] at hsum
  rw [div_eq_mul_inv]
  linarith

theorem exists_pos : ∃ r : ℝ, 0 < r ∧ ∃ f, network.IsFeasibleFlow f r :=
  exists_pos_flow network graph cap_of_adj (fun _ => rfl) (fun μ => (terminal_distance μ).1)

end Specific

end MultipleUnicast.Counterexample.Dev.Flow

namespace MultipleUnicast.Counterexample
open MultipleUnicast.Counterexample.Dev.Flow

theorem chk_flow_bound :
    feasibleRates.Nonempty ∧ BddAbove feasibleRates ∧
    (∃ r : ℝ, 0 < r ∧ ∃ f, network.IsFeasibleFlow f r) ∧
    (∀ (r : ℝ) (f : Fin network.k → Vertex → Vertex → ℝ),
      0 ≤ r → network.IsFeasibleFlow f r → r ≤ (147 : ℝ) / 157) ∧
    0 < routingThroughput ∧
    routingThroughput ≤ (735 : ℝ) / 785 ∧
    (735 : ℝ) / 785 = (147 : ℝ) / 157 ∧
    (147 : ℝ) / 157 < 1 ∧ (1 : ENNReal) ≤ codingThroughput network := by
  obtain ⟨r₀, hr₀, f₀, hf₀⟩ := exists_pos
  have hmem : r₀ ∈ feasibleRates := ⟨hr₀.le, f₀, hf₀⟩
  have hbdd : BddAbove feasibleRates := ⟨(147 : ℝ) / 157, fun r hr => by
    obtain ⟨_, f, hf⟩ := hr
    exact rate_le r f hf⟩
  have hrt : routingThroughput = sSup feasibleRates := rfl
  refine ⟨⟨r₀, hmem⟩, hbdd, ⟨r₀, hr₀, f₀, hf₀⟩, fun r f _ hf => rate_le r f hf, ?_, ?_,
    by norm_num, by norm_num, coding_rate.2.2.2.2⟩
  · rw [hrt]; exact lt_of_lt_of_le hr₀ (le_csSup hbdd hmem)
  · rw [hrt]
    refine csSup_le ⟨r₀, hmem⟩ fun r hr => ?_
    obtain ⟨_, f, hf⟩ := hr
    have := rate_le r f hf
    norm_num at this ⊢
    linarith

end MultipleUnicast.Counterexample
end

theorem solution : type_of% @MultipleUnicast.Counterexample.chk_flow_bound := @MultipleUnicast.Counterexample.chk_flow_bound
