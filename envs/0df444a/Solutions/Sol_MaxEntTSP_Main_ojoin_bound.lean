-- Prove2me | solution 1 for MaxEntTSP.Main.ojoin_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:42:19.354335+00:00
-- url     : https://prove2.me/submissions/9579788b-46cb-4eb9-8be3-ad34051f6de1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model
import Theorems.Thm_MaxEntTSP_Main_theorem_3_1
import Theorems.Thm_MaxEntTSP_Main_proposition_2_3
import Theorems.Thm_MetricTSP_tour_vector_held_karp
import Theorems.Thm_MetricTSP_tour_vector_cost
import Theorems.Thm_MetricTSP_held_karp_le_opt
import Theorems.Thm_MaxEntTSP_Main_node_split

open MaxEntTSP.Main MetricTSP Finset

namespace OJoinAux

/-! ### Parity of cuts -/

variable {N : ℕ}

/-- Number of endpoints of `e` lying in `S`. -/
noncomputable def endsIn (S : Finset (Fin N)) (e : Sym2 (Fin N)) : ℕ :=
  (S.filter (fun v => v ∈ e)).card

lemma odd_endsIn_iff (S : Finset (Fin N)) (e : Sym2 (Fin N)) (he : ¬ e.IsDiag) :
    Odd (endsIn S e) ↔ edgeCrosses S e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    have hij : i ≠ j := by simpa [Sym2.mk_isDiag_iff] using he
    have hf : S.filter (fun v => v ∈ s(i, j)) = (S.filter (· = i)) ∪ (S.filter (· = j)) := by
      ext v; simp [Sym2.mem_iff, and_or_left]
    have hdisj : Disjoint (S.filter (· = i)) (S.filter (· = j)) := by
      rw [Finset.disjoint_filter]; intro v _ h1 h2; exact hij (h1.symm.trans h2)
    unfold endsIn
    rw [hf, card_union_of_disjoint hdisj]
    have hi : (S.filter (· = i)).card = if i ∈ S then 1 else 0 := by
      rw [Finset.filter_eq']; split_ifs <;> simp
    have hj : (S.filter (· = j)).card = if j ∈ S then 1 else 0 := by
      rw [Finset.filter_eq']; split_ifs <;> simp
    rw [hi, hj]
    have hcr : edgeCrosses S s(i, j) ↔ ((i ∈ S ∧ j ∉ S) ∨ (j ∈ S ∧ i ∉ S)) := by
      constructor
      · rintro ⟨a, b, hab, h⟩
        rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h
        · exact h.symm
      · intro h; exact ⟨i, j, rfl, h⟩
    rw [hcr]
    by_cases h1 : i ∈ S <;> by_cases h2 : j ∈ S <;> simp [h1, h2]

/-- Degree-sum parity: the number of odd-degree vertices of `T` in `S` has the parity of the
number of `T`-edges crossing `S`. -/
lemma odd_card_inter_iff (T : Finset (Sym2 (Fin N))) (S : Finset (Fin N)) :
    Odd (S ∩ univ.filter (fun v => Odd (treeDeg T v))).card ↔ Odd (crossCount T S) := by
  classical
  set T' := T.filter (fun e => ¬ e.IsDiag) with hT'
  have hdeg : ∀ v, treeDeg T v = ∑ e ∈ T', if v ∈ e then 1 else 0 := by
    intro v
    rw [sum_boole, treeDeg, hT', filter_filter]
    simp
  have hsum : (∑ v ∈ S, treeDeg T v) = ∑ e ∈ T', endsIn S e := by
    simp_rw [hdeg]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro e _
    rw [sum_boole, endsIn]; simp
  have h1 : Odd (∑ v ∈ S, treeDeg T v) ↔ Odd (S ∩ univ.filter (fun v => Odd (treeDeg T v))).card := by
    rw [odd_sum_iff_odd_card_odd]
    have : S.filter (fun v => Odd (treeDeg T v)) = S ∩ univ.filter (fun v => Odd (treeDeg T v)) := by
      ext v; simp
    rw [this]
  rw [← h1, hsum, odd_sum_iff_odd_card_odd]
  have : T'.filter (fun e => Odd (endsIn S e)) = cutEdges T S := by
    ext e
    simp only [hT', mem_filter, cutEdges]
    constructor
    · rintro ⟨⟨he, hd⟩, ho⟩; exact ⟨he, (odd_endsIn_iff S e hd).mp ho⟩
    · rintro ⟨he, hc⟩
      have hd : ¬ e.IsDiag := by
        obtain ⟨a, b, rfl, h⟩ := hc
        rw [Sym2.mk_isDiag_iff]
        rintro rfl; tauto
      exact ⟨⟨he, hd⟩, (odd_endsIn_iff S e hd).mpr hc⟩
  rw [this, crossCount]

lemma even_card_odd (T : Finset (Sym2 (Fin N))) :
    Even (univ.filter (fun v => Odd (treeDeg T v))).card := by
  classical
  have h := odd_card_inter_iff T univ
  rw [univ_inter] at h
  have h0 : crossCount T univ = 0 := by
    rw [crossCount, card_eq_zero, cutEdges]
    ext e
    simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
    rintro _ ⟨a, b, _, h⟩
    simp at h
  rw [h0] at h
  rw [← Nat.not_odd_iff_even, h]
  simp

/-! ### From an `O`-join to an odd-vertex pairing (metric shortcutting) -/

lemma degree_fromEdgeSet (J : Finset (Sym2 (Fin N))) (v : Fin N)
    [DecidableRel (SimpleGraph.fromEdgeSet (J : Set (Sym2 (Fin N)))).Adj] :
    (SimpleGraph.fromEdgeSet (J : Set (Sym2 (Fin N)))).degree v =
      (J.filter (fun e => ¬ e.IsDiag ∧ v ∈ e)).card := by
  classical
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.incidenceFinset_eq_filter]
  congr 1
  ext e
  simp only [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_diff, Finset.mem_coe, Set.mem_setOf_eq]
  tauto

lemma walk_cost (c : Fin N → Fin N → ℝ) (hc : IsMetricCost c) (G : SimpleGraph (Fin N))
    {u w : Fin N} (p : G.Walk u w) :
    c u w ≤ (p.edges.map (pairCost c)).sum := by
  induction p with
  | nil => simp [hc.2.1]
  | @cons a b d h p ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
    have : pairCost c s(a, b) = c a b := by
      simp only [pairCost, Sym2.lift_mk]; rw [hc.1 b a]; ring
    rw [this]
    linarith [hc.2.2 a b d]

lemma pairCost_nonneg_of_metric (c : Fin N → Fin N → ℝ) (hc : IsMetricCost c)
    (e : Sym2 (Fin N)) : 0 ≤ pairCost c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [pairCost, Sym2.lift_mk]
    have := hc.2.2 i j i
    rw [hc.2.1 i, hc.1 j i] at this
    rw [hc.1 j i]
    linarith

/-- Shortcutting an `O`-join in a metric gives a pairing of `O` of at most its cost. -/
lemma tjoin_pairing (c : Fin N → Fin N → ℝ) (hc : IsMetricCost c) :
    ∀ (k : ℕ) (J : Finset (Sym2 (Fin N))), J.card = k → (∀ e ∈ J, ¬ e.IsDiag) →
      ∀ O : Finset (Fin N), (∀ v, Odd ((J.filter (fun e => v ∈ e)).card) ↔ v ∈ O) →
      ∃ f : Fin N → Fin N, (∀ v, f (f v) = v) ∧ (∀ v, f v ≠ v ↔ v ∈ O) ∧
        (1 / 2) * ∑ v, c v (f v) ≤ ∑ e ∈ J, pairCost c e := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro J hJk hJd O hO
  by_cases hOe : O = ∅
  · refine ⟨id, fun v => rfl, fun v => by simp [hOe], ?_⟩
    simp only [id, hc.2.1, sum_const_zero, mul_zero]
    exact sum_nonneg (fun e _ => pairCost_nonneg_of_metric c hc e)
  obtain ⟨o, ho⟩ := nonempty_iff_ne_empty.mpr hOe
  set G := SimpleGraph.fromEdgeSet (J : Set (Sym2 (Fin N))) with hG
  have hdegG : ∀ v, G.degree v = (J.filter (fun e => v ∈ e)).card := by
    intro v
    convert (degree_fromEdgeSet J v) using 2
    symm
    apply filter_congr
    intro e he
    simp [hJd e he]
  -- the component of `o`
  let H : SimpleGraph (Fin N) :=
    { Adj := fun a b => G.Adj a b ∧ G.Reachable o a
      symm := ⟨fun a b h => ⟨h.1.symm, h.2.trans h.1.reachable⟩⟩
      loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }
  have hHdeg : ∀ v, H.degree v = if G.Reachable o v then G.degree v else 0 := by
    intro v
    split_ifs with hr
    · rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
      congr 1
      ext w
      simp only [SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => h.1, fun h => ⟨h, hr⟩⟩
    · rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_zero]
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun h => hr h.2
  have hoodd : Odd (H.degree o) := by
    rw [hHdeg, if_pos (SimpleGraph.Reachable.refl o), hdegG]; exact (hO o).mpr ho
  obtain ⟨o', hne, ho'odd⟩ := H.exists_ne_odd_degree_of_exists_odd_degree o hoodd
  have hreach : G.Reachable o o' := by
    by_contra hr
    rw [hHdeg, if_neg hr] at ho'odd
    exact (Nat.not_odd_zero) ho'odd
  rw [hHdeg, if_pos hreach, hdegG] at ho'odd
  have ho' : o' ∈ O := (hO o').mp ho'odd
  obtain ⟨p⟩ := hreach
  let q := p.toPath
  have hq : (q : G.Walk o o').IsPath := q.2
  set P := (q : G.Walk o o').edges.toFinset with hP
  have hPJ : P ⊆ J := by
    intro e he
    rw [hP, List.mem_toFinset] at he
    have := (q : G.Walk o o').edges_subset_edgeSet he
    rw [hG, SimpleGraph.edgeSet_fromEdgeSet] at this
    exact this.1
  have hPne : P.Nonempty := by
    have hlen : (q : G.Walk o o').length ≠ 0 := by
      intro h
      exact hne (SimpleGraph.Walk.eq_of_length_eq_zero h).symm
    have hpos : 0 < (q : G.Walk o o').edges.length := by
      rw [SimpleGraph.Walk.length_edges]; omega
    obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hpos
    exact ⟨e, by rw [hP, List.mem_toFinset]; exact he⟩
  set J' := J \ P with hJ'
  have hJ'card : J'.card < k := by
    rw [hJ', card_sdiff_of_subset hPJ, ← hJk]
    have := hPne.card_pos
    have := card_le_card hPJ
    omega
  have hcount : ∀ v, (P.filter (fun e => v ∈ e)).card =
      (q : G.Walk o o').edges.countP (fun e => v ∈ e) := by
    intro v
    have : (P.filter (fun e => v ∈ e)) =
        ((q : G.Walk o o').edges.filter (fun e => v ∈ e)).toFinset := by
      ext e; simp [hP]
    rw [this, List.toFinset_card_of_nodup (hq.isTrail.edges_nodup.filter _),
      List.countP_eq_length_filter]
  have hdegJ' : ∀ v, (J'.filter (fun e => v ∈ e)).card + (P.filter (fun e => v ∈ e)).card =
      (J.filter (fun e => v ∈ e)).card := by
    intro v
    have hfs : J'.filter (fun e => v ∈ e) = J.filter (fun e => v ∈ e) \ P.filter (fun e => v ∈ e) := by
      ext e; simp [hJ']; tauto
    rw [hfs, card_sdiff_of_subset (filter_subset_filter _ hPJ)]
    have := card_le_card (filter_subset_filter (fun e => v ∈ e) hPJ)
    omega
  set O' := (O.erase o).erase o' with hO'
  have hO'par : ∀ v, Odd ((J'.filter (fun e => v ∈ e)).card) ↔ v ∈ O' := by
    intro v
    have h1 := hdegJ' v
    have h2 := hq.isTrail.even_countP_edges_iff v
    rw [← hcount] at h2
    have h3 := hO v
    rw [← h1, Nat.odd_add] at h3
    have hE : Even (P.filter (fun e => v ∈ e)).card ↔ (v ≠ o ∧ v ≠ o') := by
      rw [h2]; exact ⟨fun h => h hne.symm, fun h _ => h⟩
    have hmem : v ∈ O' ↔ (v ≠ o' ∧ v ≠ o ∧ v ∈ O) := by simp [hO', mem_erase]
    rw [hmem]
    by_cases hv : v = o
    · have hvO : v ∈ O := hv ▸ ho
      have hB : ¬ Even (P.filter (fun e => v ∈ e)).card := fun h => (hE.mp h).1 hv
      have hAB := h3.mpr hvO
      constructor
      · intro hA; exact absurd (hAB.mp hA) hB
      · rintro ⟨_, h, _⟩; exact absurd hv h
    · by_cases hv' : v = o'
      · have hvO : v ∈ O := hv' ▸ ho'
        have hB : ¬ Even (P.filter (fun e => v ∈ e)).card := fun h => (hE.mp h).2 hv'
        have hAB := h3.mpr hvO
        constructor
        · intro hA; exact absurd (hAB.mp hA) hB
        · rintro ⟨h, _, _⟩; exact absurd hv' h
      · have hB : Even (P.filter (fun e => v ∈ e)).card := hE.mpr ⟨hv, hv'⟩
        constructor
        · intro hA
          exact ⟨hv', hv, h3.mp ⟨fun _ => hB, fun _ => hA⟩⟩
        · rintro ⟨_, _, hvO⟩
          exact (h3.mpr hvO).mpr hB
  obtain ⟨f', hf'inv, hf'O, hf'cost⟩ := ih J'.card hJ'card J' rfl
    (fun e he => hJd e (sdiff_subset he)) O' hO'par
  have hf'o : f' o = o := by
    by_contra h; have := (hf'O o).mp h; rw [hO'] at this; simp at this
  have hf'o' : f' o' = o' := by
    by_contra h; have := (hf'O o').mp h; rw [hO'] at this; simp at this
  let f : Fin N → Fin N := fun v => if v = o then o' else if v = o' then o else f' v
  have hfo : f o = o' := by simp [f]
  have hfo' : f o' = o := by simp [f, hne]
  have hfv : ∀ v, v ≠ o → v ≠ o' → f v = f' v := by
    intro v h1 h2; simp [f, h1, h2]
  have hf'ne : ∀ v, v ≠ o → v ≠ o' → f' v ≠ o ∧ f' v ≠ o' := by
    intro v h1 h2
    constructor
    · intro h; apply h1; rw [← hf'inv v, h, hf'o]
    · intro h; apply h2; rw [← hf'inv v, h, hf'o']
  refine ⟨f, ?_, ?_, ?_⟩
  · intro v
    by_cases h1 : v = o
    · subst h1; rw [hfo, hfo']
    by_cases h2 : v = o'
    · subst h2; rw [hfo', hfo]
    rw [hfv v h1 h2, hfv _ (hf'ne v h1 h2).1 (hf'ne v h1 h2).2, hf'inv]
  · intro v
    by_cases h1 : v = o
    · subst h1; rw [hfo]; simp [hne, hne.symm, ho]
    by_cases h2 : v = o'
    · subst h2; rw [hfo']; simp [hne, hne.symm, ho']
    rw [hfv v h1 h2, hf'O v, hO', mem_erase, mem_erase]
    simp [h1, h2]
  · -- cost
    have hsplit : ∀ g : Fin N → ℝ, ∑ v, g v = g o + g o' + ∑ v ∈ (univ.erase o).erase o', g v := by
      intro g
      rw [← add_sum_erase _ _ (mem_univ o), ← add_sum_erase _ _ (mem_erase.mpr ⟨hne, mem_univ o'⟩)]
      ring
    have hrest : ∑ v ∈ (univ.erase o).erase o', c v (f v) =
        ∑ v ∈ (univ.erase o).erase o', c v (f' v) := by
      apply sum_congr rfl
      intro v hv
      simp only [mem_erase] at hv
      rw [hfv v hv.2.1 hv.1]
    rw [hsplit (fun v => c v (f v)), hsplit (fun v => c v (f' v))] at *
    rw [hfo, hfo', hrest]
    rw [hf'o, hf'o', hc.2.1, hc.2.1] at hf'cost
    have hpath : c o o' ≤ ∑ e ∈ P, pairCost c e := by
      rw [hP, List.sum_toFinset _ hq.isTrail.edges_nodup]
      exact walk_cost c hc G (q : G.Walk o o')
    have hJsplit : ∑ e ∈ J, pairCost c e = ∑ e ∈ J', pairCost c e + ∑ e ∈ P, pairCost c e := by
      rw [hJ', sum_sdiff hPJ]
    rw [hJsplit, hc.1 o' o]
    linarith

/-! ### Split tours -/

lemma proj_castSucc {n : ℕ} (u w : Fin n) : proj u (Fin.castSucc w) = w := by
  simp [proj]

lemma proj_last {n : ℕ} (u : Fin n) : proj u (Fin.last n) = u := by
  simp [proj]

lemma tspOpt_attained {N : ℕ} (c : Fin N → Fin N → ℝ) :
    ∃ π : Equiv.Perm (Fin N), tspOpt c = tourCost c π := by
  have hset : {t : ℝ | ∃ π : Equiv.Perm (Fin N), t = tourCost c π} =
      Set.range (tourCost c) := by
    ext t; simp [eq_comm]
  unfold tspOpt
  rw [hset]
  obtain ⟨π, hπ⟩ := (Set.range_nonempty (tourCost c)).csInf_mem (Set.toFinite _)
  exact ⟨π, hπ.symm⟩

lemma tour_rotate {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (d : Fin (m + 1)) :
    tourCost c (π * Equiv.addRight d) = tourCost c π := by
  unfold tourCost
  simp only [Equiv.Perm.mul_apply, Equiv.coe_addRight, finRotate_apply]
  have : ∀ i : Fin (m + 1), c (π (i + d)) (π (i + 1 + d)) =
      (fun j => c (π j) (π (j + 1))) (Equiv.addRight d i) := by
    intro i; simp only [Equiv.coe_addRight]; rw [add_right_comm]
  simp_rw [this]
  exact Equiv.sum_comp (Equiv.addRight d) (fun j => c (π j) (π (j + 1)))

lemma finRotate_castSucc {k : ℕ} (i : Fin k) :
    finRotate (k + 1) (Fin.castSucc i) = i.succ := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
  simp

/-- Cost of a split tour whose last position holds `v₀` and which otherwise follows `π`. -/
lemma split_tour_cost {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ) (u : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 2))) (π : Equiv.Perm (Fin (m + 1)))
    (hσl : σ (Fin.last (m + 1)) = Fin.last (m + 1))
    (hσc : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (π i)) :
    tourCost (splitCost c u) σ + c (π (Fin.last m)) (π 0) =
      tourCost c π + c (π (Fin.last m)) u + c u (π 0) := by
  unfold tourCost
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc (f := fun i => c (π i) (π (finRotate (m + 1) i)))]
  simp only [finRotate_castSucc, finRotate_last, Fin.succ_last, hσl, hσc]
  have h0 : (0 : Fin (m + 2)) = Fin.castSucc 0 := rfl
  rw [h0, hσc]
  have hs : ∀ j : Fin m, (Fin.castSucc j).succ = Fin.castSucc j.succ := fun j => rfl
  simp only [hs, hσc, splitCost, proj_castSucc, proj_last]
  have hr : ∀ j : Fin m, finRotate (m + 1) (Fin.castSucc j) = j.succ := fun j =>
    finRotate_castSucc j
  try simp only [hr]
  ring


/-- An optimal tour of the split instance that traverses `e₀ = {u₀, v₀}` exactly once. -/
lemma exists_split_opt_tour {m : ℕ} (hm : 1 ≤ m) (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hc : IsMetricCost c) (u : Fin (m + 1)) :
    ∃ σ : Equiv.Perm (Fin (m + 2)), tourCost (splitCost c u) σ = tspOpt c ∧
      pairCost (tourVec σ) s(u0 u, v0 (m + 1)) = 1 := by
  classical
  obtain ⟨π, hπ⟩ := tspOpt_attained c
  set d : Fin (m + 1) := π.symm u - Fin.last m
  set π₁ := π * Equiv.addRight d
  have hπ₁ : π₁ (Fin.last m) = u := by
    simp [π₁, d]
  let σ : Equiv.Perm (Fin (m + 2)) :=
    finSuccEquivLast.trans ((Equiv.optionCongr π₁).trans finSuccEquivLast.symm)
  have hσl : σ (Fin.last (m + 1)) = Fin.last (m + 1) := by
    simp [σ, finSuccEquivLast_last]
  have hσc : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (π₁ i) := by
    intro i; simp [σ, finSuccEquivLast_castSucc, finSuccEquivLast_symm_some]
  refine ⟨σ, ?_, ?_⟩
  · have h := split_tour_cost c u σ π₁ hσl hσc
    rw [hπ₁, hc.2.1 u, tour_rotate] at h
    rw [hπ]; linarith
  · set i0 : Fin (m + 2) := Fin.castSucc (Fin.last m)
    have hi0 : σ i0 = u0 u := by simp only [i0, hσc, hπ₁, u0]
    have hri0 : finRotate (m + 2) i0 = Fin.last (m + 1) := by
      simp only [i0, finRotate_castSucc, Fin.succ_last]
    have h0 : σ (finRotate (m + 2) (Fin.last (m + 1))) ≠ u0 u := by
      rw [finRotate_last]
      have : (0 : Fin (m + 2)) = Fin.castSucc 0 := rfl
      rw [this, hσc, u0]
      intro h
      have h' := Fin.castSucc_injective _ h
      rw [← hπ₁] at h'
      have := π₁.injective h'
      have : (0 : ℕ) = m := congrArg Fin.val this
      omega
    have hset : ∀ a b : Fin (m + 2), (a = u0 u ∧ b = v0 (m + 1)) ∨ (a = v0 (m + 1) ∧ b = u0 u) →
        tourSteps σ a b = {i0} := by
      intro a b hab
      ext i
      simp only [tourSteps, mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro h
        have key : (σ i = u0 u ∧ σ (finRotate (m + 2) i) = v0 (m + 1)) ∨
            (σ i = v0 (m + 1) ∧ σ (finRotate (m + 2) i) = u0 u) := by
          rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h
          · exact h.symm
        rcases key with ⟨h1, _⟩ | ⟨h1, h2⟩
        · rw [← hi0] at h1; exact σ.injective h1
        · have : i = Fin.last (m + 1) := by
            apply σ.injective; rw [h1, hσl]; rfl
          subst this
          exact absurd h2 h0
      · rintro rfl
        have key : (σ i0 = u0 u ∧ σ (finRotate (m + 2) i0) = v0 (m + 1)) := by
          rw [hi0, hri0, hσl]; exact ⟨rfl, rfl⟩
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl key
        · exact Or.inr key
    simp only [pairCost, Sym2.lift_mk, tourVec]
    rw [hset _ _ (Or.inl ⟨rfl, rfl⟩), hset _ _ (Or.inr ⟨rfl, rfl⟩)]
    simp

/-! ### Cut sums -/

lemma double_sum_eq_two_sym2 {m : ℕ} (f : Fin m → Fin m → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) =
      2 * ∑ e ∈ (univ : Finset (Sym2 (Fin m))).filter (fun e => ¬ e.IsDiag),
        Sym2.lift ⟨f, hs⟩ e := by
  rw [← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : Fin m × Fin m => s(p.1, p.2))
    (t := (univ : Finset (Sym2 (Fin m)))) (fun _ _ => mem_univ _)]
  rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not univ (fun e : Sym2 (Fin m) => e.IsDiag)]
  have h1 : ∀ e ∈ (univ : Finset (Sym2 (Fin m))).filter (fun e => e.IsDiag),
      (∑ p ∈ (univ ×ˢ univ : Finset (Fin m × Fin m)) with s(p.1, p.2) = e, f p.1 p.2) = 0 := by
    intro e he
    rw [mem_filter] at he
    apply Finset.sum_eq_zero
    intro p hp
    rw [mem_filter] at hp
    have : (s(p.1, p.2)).IsDiag := hp.2 ▸ he.2
    obtain ⟨a, b⟩ := p
    rw [Sym2.mk_isDiag_iff] at this
    simp only at this; rw [this, hd]
  rw [Finset.sum_eq_zero h1, zero_add]
  apply Finset.sum_congr rfl
  intro e he
  rw [mem_filter] at he
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using he.2
    have hfib : ((univ ×ˢ univ : Finset (Fin m × Fin m)).filter
        (fun p => s(p.1, p.2) = s(a, b))) = {(a, b), (b, a)} := by
      ext ⟨p, q⟩
      simp only [mem_filter, mem_product, mem_univ, true_and, mem_insert, mem_singleton,
        Sym2.eq_iff, Prod.mk.injEq]
    rw [hfib, Finset.sum_pair (by simp [Prod.mk.injEq, hab])]
    simp only [Sym2.lift_mk]
    rw [hs b a]
    ring

lemma pairCost_mk {m : ℕ} (c : Fin m → Fin m → ℝ) (hs : ∀ i j, c i j = c j i)
    (i j : Fin m) : pairCost c s(i, j) = c i j := by
  simp only [pairCost, Sym2.lift_mk]
  rw [hs j i]; ring


lemma edgeCrosses_mk_iff {N : ℕ} (S : Finset (Fin N)) (i j : Fin N) :
    edgeCrosses S s(i, j) ↔ ((i ∈ S ∧ j ∉ S) ∨ (j ∈ S ∧ i ∉ S)) := by
  constructor
  · rintro ⟨a, b, hab, h⟩
    rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm
  · intro h; exact ⟨i, j, rfl, h⟩

lemma cutEdges_compl {N : ℕ} (F : Finset (Sym2 (Fin N))) (S : Finset (Fin N)) :
    cutEdges F Sᶜ = cutEdges F S := by
  classical
  unfold cutEdges
  ext e
  simp only [mem_filter]
  induction e using Sym2.ind with
  | h i j =>
    rw [edgeCrosses_mk_iff, edgeCrosses_mk_iff]
    simp only [mem_compl, not_not]
    tauto

/-- The once-counted cut weight equals the sum of pair weights over crossing pairs of any
edge set containing all crossing pairs of nonzero weight. -/
lemma cut_sum_eq {N : ℕ} (w : Fin N → Fin N → ℝ) (hs : ∀ i j, w i j = w j i)
    (hd : ∀ i, w i i = 0) (F : Finset (Sym2 (Fin N))) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (S : Finset (Fin N))
    (hcov : ∀ e : Sym2 (Fin N), ¬ e.IsDiag → edgeCrosses S e → pairCost w e ≠ 0 → e ∈ F) :
    (∑ e ∈ cutEdges F S, pairCost w e) = cutW w S := by
  classical
  set f : Fin N → Fin N → ℝ := fun i j =>
    (if i ∈ S ∧ j ∉ S then w i j else 0) + (if j ∈ S ∧ i ∉ S then w i j else 0) with hf
  have hfs : ∀ i j, f i j = f j i := by
    intro i j; simp only [hf]; rw [hs i j]; ring
  have hfd : ∀ i, f i i = 0 := by intro i; simp [hf]
  have h2 : (∑ i, ∑ j, f i j) = 2 * cutW w S := by
    simp only [hf, sum_add_distrib]
    have e1 : (∑ i, ∑ j, if i ∈ S ∧ j ∉ S then w i j else 0) = cutW w S := by
      unfold cutW
      rw [← sum_filter_add_sum_filter_not univ (fun i => i ∈ S)]
      rw [sum_eq_zero (s := univ.filter (fun i => ¬ i ∈ S)), add_zero]
      · rw [filter_mem_eq_inter, univ_inter]
        apply sum_congr rfl; intro i hi
        rw [← sum_filter_add_sum_filter_not univ (fun j => j ∈ S)]
        rw [sum_eq_zero (s := univ.filter (fun j => j ∈ S)), zero_add]
        · have : univ.filter (fun j => ¬ j ∈ S) = Sᶜ := by ext; simp
          rw [this]; apply sum_congr rfl; intro j hj
          rw [if_pos ⟨hi, mem_compl.mp hj⟩]
        · intro j hj; rw [mem_filter] at hj; rw [if_neg (fun h => h.2 hj.2)]
      · intro i hi; rw [mem_filter] at hi
        apply sum_eq_zero; intro j _; rw [if_neg (fun h => hi.2 h.1)]
    have e2 : (∑ i, ∑ j, if j ∈ S ∧ i ∉ S then w i j else 0) = cutW w S := by
      rw [sum_comm]
      rw [← e1]
      apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
      rw [hs j i]
    rw [e1, e2]; ring
  have h3 := double_sum_eq_two_sym2 f hfs hfd
  rw [h2] at h3
  have h4 : cutW w S = ∑ e ∈ (univ : Finset (Sym2 (Fin N))).filter (fun e => ¬ e.IsDiag),
      Sym2.lift ⟨f, hfs⟩ e := by linarith
  rw [h4]
  have hlift : ∀ e : Sym2 (Fin N), Sym2.lift ⟨f, hfs⟩ e =
      if edgeCrosses S e then pairCost w e else 0 := by
    intro e
    induction e using Sym2.ind with
    | h i j =>
      simp only [Sym2.lift_mk, hf, edgeCrosses_mk_iff, pairCost_mk w hs]
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]
  simp_rw [hlift]
  rw [← sum_filter, filter_filter]
  unfold cutEdges
  apply sum_subset
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    exact ⟨hF e he.1, he.2⟩
  · intro e he hne
    simp only [mem_filter, mem_univ, true_and, not_and] at he hne
    by_contra h
    exact hne (hcov e he.1 he.2 h) he.2

/-- The support sum of `c · x` equals half the double sum. -/
lemma support_sum_eq {m : ℕ} (c x : Fin m → Fin m → ℝ)
    (hcs : ∀ i j, c i j = c j i) (hxs : ∀ i j, x i j = x j i)
    (hxd : ∀ i, x i i = 0) (hx0 : ∀ i j, 0 ≤ x i j) (a b : Fin m) (hcab : c a b = 0) :
    (∑ e ∈ lpSupport x a b, pairCost c e * pairCost x e) =
      (1 / 2) * ∑ i, ∑ j, c i j * x i j := by
  have hs : ∀ i j, c i j * x i j = c j i * x j i := fun i j => by rw [hcs, hxs]
  rw [double_sum_eq_two_sym2 (fun i j => c i j * x i j) hs (fun i => by simp [hxd])]
  rw [← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul]
  have hg : ∀ e : Sym2 (Fin m), pairCost c e * pairCost x e =
      Sym2.lift ⟨fun i j => c i j * x i j, hs⟩ e := by
    intro e
    induction e using Sym2.ind with
    | h i j => rw [pairCost_mk c hcs, pairCost_mk x hxs, Sym2.lift_mk]
  simp_rw [hg]
  unfold lpSupport
  apply Finset.sum_subset
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    exact he.1
  · intro e he hne
    simp only [mem_filter, mem_univ, true_and, not_and, not_lt] at he hne
    rw [← hg]
    by_cases hab : e = s(a, b)
    · subst hab; rw [pairCost_mk c hcs, hcab, zero_mul]
    · have hle := hne he hab
      have hge : 0 ≤ pairCost x e := by
        induction e using Sym2.ind with
        | h i j => rw [pairCost_mk x hxs]; exact hx0 i j
      rw [le_antisymm hle hge, mul_zero]

end OJoinAux

open OJoinAux in
theorem solution (n : ℕ) (hn : 3 ≤ n)
    (c x : Fin n → Fin n → ℝ) (hc : IsMetricCost c) (hx : IsHeldKarp x)
    (hopt : (1 / 2) * (∑ i, ∑ j, c i j * x i j) = hkValue c)
    (u : Fin n) (μ : Finset (Sym2 (Fin (n + 1))) → ℝ)
    (hμ : IsMaxEntropy (lpSupport (splitLP x u) (u0 u) (v0 n)) (splitLP x u) μ) :
    let β : ℝ := (312 / 10 ^ 18) * 10 / (1308 * 41)
    (∑ T, μ T * minMatchCost (splitCost c u) T) ≤
      (1 / 2 - (312 / 10 ^ 18 : ℝ) * β / 6) * tspOpt c := by
  classical
  intro β
  have hβdef : β = 312 / 10 ^ 18 * 10 / (1308 * 41) := rfl
  clear_value β
  obtain ⟨hc', hx', he0, hsum, hopt'⟩ := node_split n hn c x hc hx hopt u
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set c' := splitCost c u with hc'def
  set x' := splitLP x u with hx'def
  set a := u0 u with hadef
  set b := v0 (m + 1) with hbdef
  have hab : a ≠ b := by simp [hadef, hbdef, u0, v0, Fin.castSucc_ne_last]
  have hcost0 : c' a b = 0 := by
    simp only [hc'def, hadef, hbdef, splitCost, proj, u0, v0, Fin.lastCases_last,
      Fin.lastCases_castSucc, id]
    exact hc.2.1 u
  obtain ⟨σ, hσcost, hσe0⟩ := exists_split_opt_tour (m := m) (by omega) c hc u
  have hσopt : tourCost c' σ = tspOpt c' := by rw [hσcost, hopt']
  set η : ℝ := (312 / 10 ^ 18) / 1308 with hη
  have hβ : β = η * 10 / 41 := by rw [hβdef, hη]; ring
  have hβpos : 0 < β := by rw [hβdef]; norm_num
  obtain ⟨s, sS, hsS0, hs1, hcut, hsS, hs⟩ := theorem_3_1 (m + 2) (by omega) c' x' hc' hx' a b hab
    he0 hcost0 σ hσopt hσe0 μ hμ η β (by rw [hη]; norm_num) (by rw [hη]; norm_num) hβpos
  set E := lpSupport x' a b with hEdef
  set Es := tourSupport σ with hEsdef
  set τ := tourVec σ with hτdef
  have hτ := tour_vector_held_karp (m + 2) (by omega) σ
  have hτs : ∀ i j, τ i j = τ j i := hτ.1
  have hτd : ∀ i, τ i i = 0 := hτ.2.1
  have hτ0 : ∀ i j, 0 ≤ τ i j := hτ.2.2.1
  have hEd : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he; rw [hEdef, lpSupport, mem_filter] at he; exact he.2.1
  have hτnn : ∀ e, 0 ≤ pairCost τ e := by
    intro e; induction e using Sym2.ind with
    | h i j => rw [pairCost_mk τ hτs]; exact hτ0 i j
  have hxnn : ∀ e, 0 ≤ pairCost x' e := by
    intro e; induction e using Sym2.ind with
    | h i j => rw [pairCost_mk x' hx'.1]; exact hx'.2.2.1 i j
  have hEsd : ∀ e ∈ Es, ¬ e.IsDiag := by
    intro e he
    rw [hEsdef, tourSupport, mem_filter] at he
    intro hd
    induction e using Sym2.ind with
    | h i j =>
      rw [Sym2.mk_isDiag_iff] at hd
      subst hd
      have h2 := he.2
      have h0 : pairCost τ s(i, i) = 0 := by rw [pairCost_mk τ hτs]; exact hτd i
      have h0' : pairCost (tourVec σ) s(i, i) = 0 := h0
      linarith
  set e0 : Sym2 (Fin (m + 2)) := s(a, b) with he0def
  have he0d : ¬ e0.IsDiag := by rw [he0def, Sym2.mk_isDiag_iff]; exact hab
  have he0E : e0 ∉ E := by
    rw [hEdef, lpSupport, mem_filter]; intro h; exact h.2.2.1 rfl
  set F : Finset (Sym2 (Fin (m + 2))) := E ∪ Es ∪ {e0} with hFdef
  have hFd : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    rw [hFdef, mem_union, mem_union, mem_singleton] at he
    rcases he with (h | h) | h
    · exact hEd e h
    · exact hEsd e h
    · rw [h]; exact he0d
  have hEF : E ⊆ F := fun e he => by rw [hFdef]; simp [he]
  have hEsF : Es ⊆ F := fun e he => by rw [hFdef]; simp [he]
  -- the fractional O-join
  let y : Finset (Sym2 (Fin (m + 2))) → Sym2 (Fin (m + 2)) → ℝ := fun T e =>
    (if e ∈ E then pairCost x' e / 4 + s T e else 0) +
    (if e ∈ Es then pairCost τ e / 4 + sS T e else 0) + (if e = e0 then 1 else 0)
  have hβsmall : β ≤ 1 / 4 := by rw [hβdef]; norm_num
  have hy0 : ∀ T, μ T ≠ 0 → ∀ e, 0 ≤ y T e := by
    intro T hT e
    have h1 : 0 ≤ (if e ∈ E then pairCost x' e / 4 + s T e else 0) := by
      split_ifs with h
      · have h3 : -(pairCost x' e * β) ≤ s T e := by rw [← neg_mul]; exact hs1 T hT e h
        have h4 := mul_le_mul_of_nonneg_left hβsmall (hxnn e)
        linarith
      · exact le_rfl
    have h2 : 0 ≤ (if e ∈ Es then pairCost τ e / 4 + sS T e else 0) := by
      split_ifs with h
      · have := hsS0 T e; have := hτnn e; linarith
      · exact le_rfl
    have h3 : (0 : ℝ) ≤ (if e = e0 then 1 else 0) := by split_ifs <;> norm_num
    simp only [y]; linarith
  -- cut sums
  have hfilt : ∀ (G : Finset (Sym2 (Fin (m + 2)))), G ⊆ F → ∀ (S : Finset (Fin (m + 2)))
      (g : Sym2 (Fin (m + 2)) → ℝ),
      (∑ e ∈ cutEdges F S, if e ∈ G then g e else 0) = ∑ e ∈ cutEdges G S, g e := by
    intro G hG S g
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext e; simp only [cutEdges, mem_filter]
    constructor
    · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨hG h1, h2⟩, h1⟩
  have hcutsplit : ∀ T S, (∑ e ∈ cutEdges F S, y T e) =
      (∑ e ∈ cutEdges E S, (pairCost x' e / 4 + s T e)) +
      (∑ e ∈ cutEdges Es S, (pairCost τ e / 4 + sS T e)) +
      (if edgeCrosses S e0 then 1 else 0) := by
    intro T S
    have hy : ∀ e, y T e = (if e ∈ E then pairCost x' e / 4 + s T e else 0) +
        (if e ∈ Es then pairCost τ e / 4 + sS T e else 0) + (if e = e0 then 1 else 0) :=
      fun e => rfl
    rw [sum_congr rfl (fun e _ => hy e), sum_add_distrib, sum_add_distrib, hfilt E hEF,
      hfilt Es hEsF, sum_ite_eq']
    congr 1
    have : e0 ∈ cutEdges F S ↔ edgeCrosses S e0 := by
      simp only [cutEdges, mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨by rw [hFdef]; simp, h⟩⟩
    by_cases h : edgeCrosses S e0
    · rw [if_pos (this.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (this.mp h')), if_neg h]
  have hcutx : ∀ S : Finset (Fin (m + 2)), ¬ edgeCrosses S e0 →
      (∑ e ∈ cutEdges E S, pairCost x' e) = cutW x' S := by
    intro S hS
    apply cut_sum_eq x' hx'.1 hx'.2.1 E hEd S
    intro e hd hcr hne
    rw [hEdef, lpSupport, mem_filter]
    refine ⟨mem_univ _, hd, ?_, lt_of_le_of_ne (hxnn e) (Ne.symm hne)⟩
    rintro rfl; exact hS hcr
  have hcutτ : ∀ S : Finset (Fin (m + 2)),
      (∑ e ∈ cutEdges Es S, pairCost τ e) = cutW τ S := by
    intro S
    apply cut_sum_eq τ hτ.1 hτ.2.1 Es hEsd S
    intro e hd hcr hne
    rw [hEsdef, tourSupport, mem_filter]
    exact ⟨mem_univ _, lt_of_le_of_ne (hτnn e) (Ne.symm hne)⟩
  have hzcut : ∀ S, cutW (zVector x' σ) S = (cutW x' S + cutW τ S) / 2 := by
    intro S
    simp only [cutW, zVector, hτdef]
    rw [← sum_add_distrib, sum_div]
    apply sum_congr rfl; intro i _
    rw [← sum_add_distrib, sum_div]
  -- main feasibility claim on cuts avoiding both copies
  have hfeas0 : ∀ T, μ T ≠ 0 → ∀ S : Finset (Fin (m + 2)), a ∉ S → b ∉ S →
      Odd (S ∩ univ.filter (fun v => Odd (treeDeg T v))).card →
      1 ≤ ∑ e ∈ cutEdges F S, y T e := by
    intro T hT S haS hbS hodd
    have hnc : ¬ edgeCrosses S e0 := by
      rw [he0def, edgeCrosses_mk_iff]; tauto
    have hSne : S.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      rw [h, empty_inter] at hodd
      simp at hodd
    have hSu : S ≠ univ := by
      intro h; rw [h] at haS; exact haS (mem_univ _)
    rw [hcutsplit, if_neg hnc, add_zero, sum_add_distrib, sum_add_distrib, ← sum_div, ← sum_div,
      hcutx S hnc, hcutτ S]
    have hX : 2 ≤ cutW x' S := hx'.2.2.2.2.2 S hSne hSu
    have hT2 : 2 ≤ cutW τ S := hτ.2.2.2.2.2 S hSne hSu
    have hsS : 0 ≤ ∑ e ∈ cutEdges Es S, sS T e := sum_nonneg (fun e _ => hsS0 T e)
    have hcc : Odd (crossCount T S) := (odd_card_inter_iff T S).mp hodd
    by_cases hnear : cutW (zVector x' σ) S ≤ 2 + η
    · have := hcut T hT S ⟨hSne, haS, hbS, hnear⟩ hcc
      simp only [randomCutSum] at this
      linarith
    · push Not at hnear
      rw [hzcut] at hnear
      have hs_lb : -(β * cutW x' S) ≤ ∑ e ∈ cutEdges E S, s T e := by
        rw [← hcutx S hnc, mul_sum, ← sum_neg_distrib]
        apply sum_le_sum
        intro e he
        have := hs1 T hT e (mem_filter.mp he).1
        linarith
      rw [hβdef] at hs_lb
      rw [hη] at hnear
      nlinarith
  have hfeas : ∀ T, μ T ≠ 0 → OJoinFeasible F (univ.filter (fun v => Odd (treeDeg T v))) (y T) := by
    intro T hT
    refine ⟨fun e _ => hy0 T hT e, ?_⟩
    intro S hodd
    by_cases hcr : edgeCrosses S e0
    · have hmem : e0 ∈ cutEdges F S := by
        simp only [cutEdges, mem_filter]; exact ⟨by rw [hFdef]; simp, hcr⟩
      have h1 : y T e0 ≤ ∑ e ∈ cutEdges F S, y T e :=
        single_le_sum (f := y T) (fun e _ => hy0 T hT e) hmem
      have h2 : 1 ≤ y T e0 := by
        have hyv : y T e0 = (if e0 ∈ E then pairCost x' e0 / 4 + s T e0 else 0) +
            (if e0 ∈ Es then pairCost τ e0 / 4 + sS T e0 else 0) +
            (if e0 = e0 then 1 else 0) := rfl
        rw [hyv, if_neg he0E, if_pos rfl]
        have : 0 ≤ (if e0 ∈ Es then pairCost τ e0 / 4 + sS T e0 else 0) := by
          split_ifs
          · have := hsS0 T e0; have := hτnn e0; linarith
          · exact le_rfl
        linarith
      linarith
    · have hab' : (a ∈ S ↔ b ∈ S) := by
        rw [he0def, edgeCrosses_mk_iff] at hcr; tauto
      by_cases haS : a ∈ S
      · have hbS : b ∈ S := hab'.mp haS
        rw [← cutEdges_compl]
        apply hfeas0 T hT Sᶜ (fun h => (mem_compl.mp h) haS) (fun h => (mem_compl.mp h) hbS)
        have hev := even_card_odd T
        set O := univ.filter (fun v => Odd (treeDeg T v))
        have hsplit : (S ∩ O).card + (Sᶜ ∩ O).card = O.card := by
          rw [← card_union_of_disjoint]
          · congr 1; ext v; simp; tauto
          · rw [disjoint_left]; intro v h1 h2; simp at h1 h2; exact h2.1 h1.1
        rw [← hsplit] at hev
        rcases hodd with ⟨k1, hk1⟩
        rcases hev with ⟨k2, hk2⟩
        exact ⟨k2 - k1 - 1, by omega⟩
      · exact hfeas0 T hT S haS (fun h => haS (hab'.mpr h)) hodd
  -- per-tree matching bound
  have hc'nn : ∀ e, 0 ≤ pairCost c' e := fun e => pairCost_nonneg_of_metric c' hc' e
  have hmatch : ∀ T, μ T ≠ 0 → minMatchCost c' T ≤ ∑ e ∈ F, pairCost c' e * y T e := by
    intro T hT
    set O := univ.filter (fun v => Odd (treeDeg T v)) with hOdef
    obtain ⟨hp1, _⟩ := proposition_2_3 (m + 2) F hFd c' (fun e _ => hc'nn e) O (even_card_odd T)
    obtain ⟨J, hJ, hJc⟩ := hp1 (y T) (hfeas T hT)
    have hJd : ∀ e ∈ J, ¬ e.IsDiag := by
      intro e he
      have := hJ.1 (Finset.mem_coe.mpr he)
      exact SimpleGraph.not_isDiag_of_mem_edgeSet _ this
    obtain ⟨f, hfinv, hfO, hfcost⟩ := tjoin_pairing c' hc' J.card J rfl hJd O
      (fun v => hJ.2 v)
    have hpair : IsOddPairing T f := ⟨hfinv, fun v => by rw [hfO v, hOdef]; simp⟩
    have hle : minMatchCost c' T ≤ (1 / 2) * ∑ v, c' v (f v) := by
      unfold minMatchCost
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro t ⟨g, hg, rfl⟩
        apply mul_nonneg (by norm_num)
        apply sum_nonneg; intro v _
        have := hc'.2.2 v (g v) v
        rw [hc'.2.1 v, hc'.1 (g v) v] at this
        linarith
      · exact ⟨f, hpair, rfl⟩
    linarith
  -- expected cost of the fractional O-join
  have hFsum : ∀ T, (∑ e ∈ F, pairCost c' e * y T e) =
      (∑ e ∈ E, pairCost c' e * (pairCost x' e / 4 + s T e)) +
      (∑ e ∈ Es, pairCost c' e * (pairCost τ e / 4 + sS T e)) := by
    intro T
    have h1 : (∑ e ∈ F, pairCost c' e * (if e ∈ E then pairCost x' e / 4 + s T e else 0)) =
        ∑ e ∈ E, pairCost c' e * (pairCost x' e / 4 + s T e) := by
      simp_rw [mul_ite, mul_zero]
      rw [sum_ite_mem, inter_eq_right.mpr hEF]
    have h2 : (∑ e ∈ F, pairCost c' e * (if e ∈ Es then pairCost τ e / 4 + sS T e else 0)) =
        ∑ e ∈ Es, pairCost c' e * (pairCost τ e / 4 + sS T e) := by
      simp_rw [mul_ite, mul_zero]
      rw [sum_ite_mem, inter_eq_right.mpr hEsF]
    have h3 : (∑ e ∈ F, pairCost c' e * (if e = e0 then (1 : ℝ) else 0)) = 0 := by
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [sum_ite_eq']
      split_ifs
      · rw [he0def, pairCost_mk c' hc'.1, hcost0]
      · rfl
    have hy : ∀ e, pairCost c' e * y T e =
        pairCost c' e * (if e ∈ E then pairCost x' e / 4 + s T e else 0) +
        pairCost c' e * (if e ∈ Es then pairCost τ e / 4 + sS T e else 0) +
        pairCost c' e * (if e = e0 then 1 else 0) := by
      intro e; simp only [y]; ring
    rw [sum_congr rfl (fun e _ => hy e), sum_add_distrib, sum_add_distrib, h1, h2, h3, add_zero]
  have hμsum : (∑ T, μ T) = 1 := hμ.1.2.2.1
  have hμnn : ∀ T, 0 ≤ μ T := hμ.1.1
  have hstep1 : (∑ T, μ T * minMatchCost c' T) ≤
      ∑ T, μ T * ((∑ e ∈ E, pairCost c' e * (pairCost x' e / 4 + s T e)) +
        (∑ e ∈ Es, pairCost c' e * (pairCost τ e / 4 + sS T e))) := by
    apply sum_le_sum
    intro T _
    by_cases hT : μ T = 0
    · rw [hT, zero_mul, zero_mul]
    · rw [← hFsum T]
      exact mul_le_mul_of_nonneg_left (hmatch T hT) (hμnn T)
  -- H = hkValue
  set H := ∑ e ∈ E, pairCost c' e * pairCost x' e with hHdef
  have hH : H = hkValue c := by
    rw [hHdef, hEdef, support_sum_eq c' x' hc'.1 hx'.1 hx'.2.1 hx'.2.2.1 a b hcost0, hsum, hopt]
  set Opt := ∑ e ∈ Es, pairCost c' e * pairCost τ e with hOptdef
  have hOpt : Opt = tspOpt c := by
    rw [hOptdef]
    have hsymm : ∀ i j, (fun i j => c' i j * τ i j) i j = (fun i j => c' i j * τ i j) j i := by
      intro i j; show c' i j * τ i j = c' j i * τ j i; rw [hc'.1 i j, hτs i j]
    have hfull := double_sum_eq_two_sym2 (fun i j => c' i j * τ i j) hsymm
      (fun i => by simp [hτd])
    rw [tour_vector_cost (m + 2) (by omega) c' hc'.1 σ, hσcost] at hfull
    have hpt : ∀ e : Sym2 (Fin (m + 2)),
        Sym2.lift ⟨fun i j => c' i j * τ i j, hsymm⟩ e = pairCost c' e * pairCost τ e := by
      intro e
      induction e using Sym2.ind with
      | h i j => rw [pairCost_mk c' hc'.1, pairCost_mk τ hτs, Sym2.lift_mk]
    simp only [hpt] at hfull
    have : (∑ e ∈ Es, pairCost c' e * pairCost τ e) =
        ∑ e ∈ (univ : Finset (Sym2 (Fin (m + 2)))).filter (fun e => ¬ e.IsDiag),
          pairCost c' e * pairCost τ e := by
      apply sum_subset
      · intro e he
        simp only [mem_filter, mem_univ, true_and]; exact hEsd e he
      · intro e _ hne
        have hz : pairCost τ e = 0 := by
          rw [hEsdef, tourSupport, mem_filter] at hne
          simp only [mem_univ, true_and, not_lt] at hne
          exact le_antisymm hne (hτnn e)
        rw [hz, mul_zero]
    rw [this]; linarith
  have hτge1 : ∀ e ∈ Es, 1 ≤ pairCost τ e := by
    intro e he
    rw [hEsdef, tourSupport, mem_filter] at he
    induction e using Sym2.ind with
    | h i j =>
      rw [pairCost_mk τ hτs] at he ⊢
      have hpos := he.2
      simp only [hτdef, tourVec] at hpos ⊢
      have : 0 < (tourSteps σ i j).card := by exact_mod_cast hpos
      exact_mod_cast this
  -- linearity of expectation
  have hstep2 : (∑ T, μ T * ((∑ e ∈ E, pairCost c' e * (pairCost x' e / 4 + s T e)) +
        (∑ e ∈ Es, pairCost c' e * (pairCost τ e / 4 + sS T e)))) =
      H / 4 + (∑ e ∈ E, pairCost c' e * ∑ T, μ T * s T e) + Opt / 4 +
        (∑ e ∈ Es, pairCost c' e * ∑ T, μ T * sS T e) := by
    simp only [mul_add, sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (s := univ) (t := E), Finset.sum_comm (s := univ) (t := Es)]
    rw [Finset.sum_comm (s := univ) (t := E), Finset.sum_comm (s := univ) (t := Es)]
    have e1 : ∀ e, (∑ T, μ T * (pairCost c' e * (pairCost x' e / 4))) =
        pairCost c' e * pairCost x' e / 4 := by
      intro e; rw [← sum_mul, hμsum]; ring
    have e2 : ∀ e, (∑ T, μ T * (pairCost c' e * (pairCost τ e / 4))) =
        pairCost c' e * pairCost τ e / 4 := by
      intro e; rw [← sum_mul, hμsum]; ring
    have e3 : ∀ e, (∑ T, μ T * (pairCost c' e * s T e)) = ∑ T, pairCost c' e * (μ T * s T e) := by
      intro e; apply sum_congr rfl; intro T _; ring
    have e4 : ∀ e, (∑ T, μ T * (pairCost c' e * sS T e)) =
        ∑ T, pairCost c' e * (μ T * sS T e) := by
      intro e; apply sum_congr rfl; intro T _; ring
    simp_rw [e1, e2, e3, e4]
    rw [hHdef, hOptdef, sum_div, sum_div]
    ring
  have hb1 : (∑ e ∈ E, pairCost c' e * ∑ T, μ T * s T e) ≤
      -(1 / 3 : ℝ) * epsP * β * H := by
    rw [hHdef, mul_sum]
    apply sum_le_sum
    intro e he
    have := hs e he
    have := hc'nn e
    have h := mul_le_mul_of_nonneg_left (hs e he) (hc'nn e)
    linarith
  have hb2 : (∑ e ∈ Es, pairCost c' e * ∑ T, μ T * sS T e) ≤ 218 * η * β * Opt := by
    rw [hOptdef, mul_sum]
    apply sum_le_sum
    intro e he
    have h1 := mul_le_mul_of_nonneg_left (hsS e he) (hc'nn e)
    have h2 : 0 ≤ 218 * η * β := by rw [hη]; positivity
    have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hτge1 e he) (hc'nn e)) h2
    nlinarith
  have hHle : H ≤ Opt := by rw [hH, hOpt]; exact held_karp_le_opt (m + 1) hn c hc
  have hfinal := hstep1
  rw [hstep2] at hfinal
  rw [← hOpt]
  simp only [epsP] at hb1
  rw [hβdef] at hb1 hb2 ⊢
  rw [hη] at hb2
  nlinarith
