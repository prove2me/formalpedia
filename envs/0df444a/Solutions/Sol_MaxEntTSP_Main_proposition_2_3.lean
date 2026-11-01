-- Prove2me | solution 1 for MaxEntTSP.Main.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:48:08.448715+00:00
-- url     : https://prove2.me/submissions/640db287-2e03-47f9-9e2a-49f746119414

import Mathlib
import Definitions.Def_MaxEntTSP_Main_OJoin
import Definitions.Def_MetricGenerators_FewComponents_TJoin
import Theorems.Thm_ChinesePostman_Polyhedron_postman_polyhedron

open MaxEntTSP.Main MetricTSP Finset

namespace P23Aux

variable {m : ℕ}

lemma edgeCrosses_mk_iff (S : Finset (Fin m)) (i j : Fin m) :
    edgeCrosses S s(i, j) ↔ ((i ∈ S ∧ j ∉ S) ∨ (j ∈ S ∧ i ∉ S)) := by
  constructor
  · rintro ⟨a, b, hab, h⟩
    rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm
  · intro h; exact ⟨i, j, rfl, h⟩

/-- Number of endpoints of `e` lying in `S`. -/
noncomputable def endsIn (S : Finset (Fin m)) (e : Sym2 (Fin m)) : ℕ :=
  (S.filter (fun v => v ∈ e)).card

lemma odd_endsIn_iff (S : Finset (Fin m)) (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) :
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
    rw [hi, hj, edgeCrosses_mk_iff]
    by_cases h1 : i ∈ S <;> by_cases h2 : j ∈ S <;> simp [h1, h2]

open Classical in
/-- For a loopless edge set `J`, the number of vertices of `S` of odd `J`-degree has the parity
of the number of `J`-edges crossing `S`. -/
lemma odd_card_iff_odd_cross (J : Finset (Sym2 (Fin m))) (hJ : ∀ e ∈ J, ¬ e.IsDiag)
    (S : Finset (Fin m)) :
    Odd (S.filter (fun v => Odd (J.filter (fun e => v ∈ e)).card)).card ↔
      Odd (J.filter (edgeCrosses S)).card := by
  classical
  have hsum : (∑ v ∈ S, (J.filter (fun e => v ∈ e)).card) = ∑ e ∈ J, endsIn S e := by
    have : ∀ v, (J.filter (fun e => v ∈ e)).card = ∑ e ∈ J, if v ∈ e then 1 else 0 := by
      intro v; rw [sum_boole]; simp
    simp_rw [this]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro e _
    rw [sum_boole, endsIn]; simp
  rw [← odd_sum_iff_odd_card_odd, hsum, odd_sum_iff_odd_card_odd]
  rw [filter_congr (fun e he => odd_endsIn_iff S e (hJ e he))]

lemma int_sum_modEq (A : Finset (Sym2 (Fin m))) (z : Sym2 (Fin m) → ℤ) :
    (∑ e ∈ A, z e) ≡ ((A.filter (fun e => Odd (z e))).card : ℤ) [ZMOD 2] := by
  classical
  unfold Int.ModEq
  rw [Finset.sum_int_mod]
  have : ∀ e, z e % 2 = if Odd (z e) then 1 else 0 := by
    intro e
    split_ifs with h
    · exact Int.odd_iff.mp h
    · exact Int.even_iff.mp (Int.not_odd_iff_even.mp h)
  simp_rw [this]
  rw [sum_boole]

end P23Aux

open P23Aux in
theorem solution (m : ℕ) (F : Finset (Sym2 (Fin m)))
    (hloop : ∀ e ∈ F, ¬ e.IsDiag)
    (c : Fin m → Fin m → ℝ) (hc : ∀ e ∈ F, 0 ≤ pairCost c e)
    (O : Finset (Fin m)) (hO : Even O.card) :
    (∀ y : Sym2 (Fin m) → ℝ, OJoinFeasible F O y →
      ∃ J : Finset (Sym2 (Fin m)),
        MetricGenerators.FewComponents.IsTJoin (MetricGenerators.FewComponents.edgeGraph F) O J ∧
        (∑ e ∈ J, pairCost c e) ≤ ∑ e ∈ F, pairCost c e * y e) ∧
    (∀ J : Finset (Sym2 (Fin m)),
      MetricGenerators.FewComponents.IsTJoin (MetricGenerators.FewComponents.edgeGraph F) O J →
      OJoinFeasible F O (fun e => if e ∈ J then 1 else 0)) := by
  classical
  -- edges of `edgeGraph F` are exactly `F`
  have hedge : (MetricGenerators.FewComponents.edgeGraph F).edgeSet = (F : Set (Sym2 (Fin m))) := by
    unfold MetricGenerators.FewComponents.edgeGraph
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff, Finset.mem_coe, Set.mem_setOf_eq, and_iff_left_iff_imp]
    exact hloop e
  constructor
  · intro y hy
    -- vertices whose `F`-degree parity disagrees with membership in `O`
    set deg : Fin m → ℕ := fun v => (F.filter (fun e => v ∈ e)).card with hdeg
    set D : Finset (Fin m) := univ.filter (fun v => ¬ (Odd (deg v) ↔ v ∈ O)) with hD
    -- the gadget graph: a new vertex `none` joined to every vertex of `D`
    let E' := {e // e ∈ F} ⊕ {d // d ∈ D}
    let ends' : E' → Sym2 (Option (Fin m)) :=
      Sum.elim (fun e => e.val.map some) (fun d => s(some d.val, none))
    have hl' : ∀ e', ¬ (ends' e').IsDiag := by
      intro e'
      rcases e' with e | d
      · simp only [ends', Sum.elim_inl]
        rw [Sym2.isDiag_map (Option.some_injective _)]
        exact hloop e.val e.2
      · simp [ends', Sym2.mk_isDiag_iff]
    let G' : ChinesePostman.Polyhedron.Graph (Option (Fin m)) E' := ⟨ends', hl'⟩
    have hmemmap : ∀ (v : Fin m) (e : Sym2 (Fin m)), some v ∈ e.map some ↔ v ∈ e := by
      intro v e
      rw [Sym2.mem_map]
      constructor
      · rintro ⟨a, ha, h⟩; rw [Option.some_inj] at h; rw [← h]; exact ha
      · intro h; exact ⟨v, h, rfl⟩
    have hnonemap : ∀ e : Sym2 (Fin m), (none : Option (Fin m)) ∉ e.map some := by
      intro e h
      rw [Sym2.mem_map] at h
      obtain ⟨a, _, h⟩ := h
      exact Option.some_ne_none a h
    -- degrees in the gadget graph
    have hdeg_some : ∀ v, ChinesePostman.Polyhedron.degree G' (some v) =
        deg v + if v ∈ D then 1 else 0 := by
      intro v
      unfold ChinesePostman.Polyhedron.degree
      rw [card_filter, Fintype.sum_sum_type]
      congr 1
      · simp only [G', ends', Sum.elim_inl, hmemmap]
        rw [hdeg]
        simp only
        rw [card_filter]
        exact Finset.sum_coe_sort F (fun e => if v ∈ e then 1 else 0)
      · simp only [G', ends', Sum.elim_inr, Sym2.mem_iff, Option.some_inj, reduceCtorEq, or_false]
        rw [Finset.sum_coe_sort D (fun d => if v = d then 1 else 0)]
        rw [sum_ite_eq]
    have hdeg_none : ChinesePostman.Polyhedron.degree G' none = D.card := by
      unfold ChinesePostman.Polyhedron.degree
      rw [card_filter, Fintype.sum_sum_type]
      simp only [G', ends', Sum.elim_inl, Sum.elim_inr, hnonemap, if_false, sum_const_zero,
        zero_add, Sym2.mem_iff, reduceCtorEq, false_or, if_true, sum_const, card_univ,
        Fintype.card_coe, smul_eq_mul, mul_one]
    have hodd_some : ∀ v, Odd (ChinesePostman.Polyhedron.degree G' (some v)) ↔ v ∈ O := by
      intro v
      rw [hdeg_some]
      by_cases hv : v ∈ D
      · rw [if_pos hv, Nat.odd_add_one]
        have := hv; rw [hD, mem_filter] at this
        tauto
      · rw [if_neg hv, add_zero]
        have := hv; rw [hD, mem_filter] at this
        simp only [mem_univ, true_and, not_not] at this
        exact this
    have hDeven : Even D.card := by
      have hA : Even (univ.filter (fun v => Odd (deg v))).card := by
        have h := odd_card_iff_odd_cross F hloop univ
        have h0 : F.filter (edgeCrosses univ) = ∅ := by
          ext e; simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro _ ⟨a, b, _, h⟩; simp at h
        rw [h0, card_empty] at h
        rw [← Nat.not_odd_iff_even]
        intro hc; exact (Nat.not_odd_zero) (h.mp hc)
      set A := univ.filter (fun v => Odd (deg v)) with hAdef
      have hDeq : D = (A \ O) ∪ (O \ A) := by
        ext v; simp only [hD, hAdef, mem_filter, mem_univ, true_and, mem_union, mem_sdiff]
        tauto
      have hdisj : Disjoint (A \ O) (O \ A) := by
        rw [disjoint_left]; intro v h1 h2
        exact (mem_sdiff.mp h1).2 (mem_sdiff.mp h2).1
      rw [hDeq, card_union_of_disjoint hdisj]
      have e1 := card_sdiff_add_card_inter A O
      have e2 := card_sdiff_add_card_inter O A
      rw [inter_comm] at e2
      obtain ⟨a, ha⟩ := hA
      obtain ⟨o, ho⟩ := hO
      exact ⟨a + o - (A ∩ O).card, by omega⟩
    -- odd sets of the gadget graph
    have hoddset : ∀ S' : Finset (Option (Fin m)), ChinesePostman.Polyhedron.IsOddSet G' S' →
        Odd ((univ.filter (fun v => some v ∈ S')) ∩ O).card := by
      intro S' hS'
      unfold ChinesePostman.Polyhedron.IsOddSet at hS'
      have heq : S'.filter (fun n => Odd (ChinesePostman.Polyhedron.degree G' n)) =
          ((univ.filter (fun v => some v ∈ S')) ∩ O).map ⟨some, Option.some_injective _⟩ := by
        ext n
        rcases n with _ | v
        · simp only [mem_filter, mem_map, Function.Embedding.coeFn_mk, reduceCtorEq, and_false,
            exists_false, iff_false, not_and]
          intro _
          rw [hdeg_none, Nat.not_odd_iff_even]; exact hDeven
        · simp only [mem_filter, mem_map, mem_inter, mem_univ, true_and,
            Function.Embedding.coeFn_mk, Option.some_inj, exists_eq_right, hodd_some]
      rw [heq, card_map] at hS'
      exact hS'
    -- cut sums of the extended vector
    let y' : E' → ℝ := Sum.elim (fun e => y e.val) (fun _ => 0)
    have hmeets : ∀ (S' : Finset (Option (Fin m))) (e : {e // e ∈ F}),
        ChinesePostman.Polyhedron.Meets G' (Sum.inl e) S' ↔
          edgeCrosses (univ.filter (fun v => some v ∈ S')) e.val := by
      intro S' ⟨e, he⟩
      simp only [ChinesePostman.Polyhedron.Meets, G', ends', Sum.elim_inl]
      induction e using Sym2.ind with
      | h i j =>
        rw [edgeCrosses_mk_iff]
        simp only [Sym2.map_mk, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨a, b, hab, ha, hb⟩
          rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left; rw [h1, h2]; exact ⟨ha, hb⟩
          · right; rw [h1, h2]; exact ⟨ha, hb⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨some i, some j, rfl, h1, h2⟩
          · exact ⟨some j, some i, Sym2.eq_swap, h1, h2⟩
    have hcutsum : ∀ S' : Finset (Option (Fin m)),
        ChinesePostman.Polyhedron.cutSum G' y' S' =
          ∑ e ∈ cutEdges F (univ.filter (fun v => some v ∈ S')), y e := by
      intro S'
      unfold ChinesePostman.Polyhedron.cutSum
      rw [sum_filter, Fintype.sum_sum_type]
      simp only [y', Sum.elim_inl, Sum.elim_inr, ite_self, sum_const_zero, add_zero, hmeets]
      rw [Finset.sum_coe_sort F (fun e => if edgeCrosses (univ.filter (fun v => some v ∈ S')) e
        then y e else 0)]
      unfold cutEdges
      rw [sum_filter]
    have hpoly : y' ∈ ChinesePostman.Polyhedron.postmanPolyhedron G' := by
      refine ⟨?_, ?_⟩
      · intro e'
        rcases e' with e | d
        · exact hy.1 e.val e.2
        · exact le_rfl
      · intro S' hS'
        rw [hcutsum]
        exact hy.2 _ (hoddset S' hS')
    rw [← ChinesePostman.Polyhedron.postman_polyhedron G', _root_.convexHull_eq] at hpoly
    obtain ⟨ι, t, w, z, hw0, hw1, hz, hcm⟩ := hpoly
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcm
    -- the cost functional on the `F`-coordinates
    let cost : (E' → ℝ) → ℝ := fun x => ∑ e : {e // e ∈ F}, pairCost c e.val * x (Sum.inl e)
    have hcost_y : cost y' = ∑ e ∈ F, pairCost c e * y e := by
      simp only [cost, y', Sum.elim_inl]
      exact Finset.sum_coe_sort F (fun e => pairCost c e * y e)
    have hcost_lin : cost y' = ∑ i ∈ t, w i * cost (z i) := by
      rw [← hcm]
      simp only [cost, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply sum_congr rfl; intro e _; apply sum_congr rfl; intro i _; ring
    -- some point of positive weight is no more expensive than `y`
    obtain ⟨i, hi, hwi, hci⟩ : ∃ i ∈ t, 0 < w i ∧ cost (z i) ≤ cost y' := by
      by_contra hcon
      push Not at hcon
      have hpos : ∃ i ∈ t, 0 < w i := by
        by_contra h
        push Not at h
        have : ∑ i ∈ t, w i ≤ 0 := sum_nonpos h
        linarith
      obtain ⟨i0, hi0, hw0pos⟩ := hpos
      have hlt : ∑ i ∈ t, w i * cost y' < ∑ i ∈ t, w i * cost (z i) := by
        apply sum_lt_sum
        · intro i hi
          rcases (hw0 i hi).lt_or_eq with h | h
          · exact (mul_lt_mul_of_pos_left (hcon i hi h) h).le
          · rw [← h, zero_mul, zero_mul]
        · exact ⟨i0, hi0, mul_lt_mul_of_pos_left (hcon i0 hi0 hw0pos) hw0pos⟩
      rw [← sum_mul, hw1, one_mul, ← hcost_lin] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨zz, hzz0, hzzpar, hzzeq⟩ := hz i hi
    -- the gadget coordinates of `z i` vanish
    have hgad : ∀ d : {d // d ∈ D}, zz (Sum.inr d) = 0 := by
      intro d
      have h0 : y' (Sum.inr d) = ∑ j ∈ t, w j * z j (Sum.inr d) := by
        rw [← hcm]; simp [Finset.sum_apply]
      simp only [y', Sum.elim_inr] at h0
      have hnn : ∀ j ∈ t, 0 ≤ w j * z j (Sum.inr d) := by
        intro j hj
        obtain ⟨zj, hzj0, _, hzjeq⟩ := hz j hj
        rw [hzjeq]
        exact mul_nonneg (hw0 j hj) (by show (0 : ℝ) ≤ (zj (Sum.inr d) : ℝ); exact_mod_cast hzj0 _)
      have := (sum_eq_zero_iff_of_nonneg hnn).mp h0.symm i hi
      rw [hzzeq] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hwi.ne'
      · have h' : ((zz (Sum.inr d) : ℤ) : ℝ) = 0 := h
        exact_mod_cast h'
    -- the join
    let zF : Sym2 (Fin m) → ℤ := fun e => if h : e ∈ F then zz (Sum.inl ⟨e, h⟩) else 0
    have hzF0 : ∀ e, 0 ≤ zF e := by
      intro e; simp only [zF]; split_ifs
      · exact hzz0 _
      · exact le_rfl
    set J := F.filter (fun e => Odd (zF e)) with hJdef
    refine ⟨J, ⟨?_, ?_⟩, ?_⟩
    · intro e he
      rw [hedge]
      exact (mem_filter.mp (Finset.mem_coe.mp he)).1
    · intro v
      unfold MetricGenerators.FewComponents.edgeDeg
      have hpv := hzzpar (some v)
      unfold ChinesePostman.Polyhedron.incidentSum ChinesePostman.Polyhedron.bParity at hpv
      rw [sum_filter, Fintype.sum_sum_type] at hpv
      simp only [G', ends', Sum.elim_inl, Sum.elim_inr, hmemmap, hgad, ite_self,
        sum_const_zero, add_zero, hodd_some] at hpv
      have hsF : (∑ e : {e // e ∈ F}, if v ∈ e.val then zz (Sum.inl e) else 0) =
          ∑ e ∈ F.filter (fun e => v ∈ e), zF e := by
        rw [sum_filter]
        rw [← Finset.sum_coe_sort F (fun e => if v ∈ e then zF e else 0)]
        apply sum_congr rfl
        intro e _
        simp only [zF, dif_pos e.2]
      rw [hsF] at hpv
      have hmod := (int_sum_modEq (F.filter (fun e => v ∈ e)) zF).symm.trans hpv
      have hfj : (F.filter (fun e => v ∈ e)).filter (fun e => Odd (zF e)) =
          J.filter (fun e => v ∈ e) := by
        ext e; simp only [hJdef, mem_filter]; tauto
      rw [hfj] at hmod
      by_cases hvO : v ∈ O
      · rw [if_pos hvO] at hmod
        simp only [hvO, iff_true]
        have : ((J.filter (fun e => v ∈ e)).card : ℤ) % 2 = 1 := hmod
        have h2 : Odd ((J.filter (fun e => v ∈ e)).card : ℤ) := Int.odd_iff.mpr this
        exact_mod_cast h2
      · rw [if_neg hvO] at hmod
        simp only [hvO, iff_false]
        have : ((J.filter (fun e => v ∈ e)).card : ℤ) % 2 = 0 := hmod
        have h2 : Even ((J.filter (fun e => v ∈ e)).card : ℤ) := Int.even_iff.mpr this
        rw [Nat.not_odd_iff_even]
        exact_mod_cast h2
    · -- cost
      have hcz : cost (z i) = ∑ e ∈ F, pairCost c e * (zF e : ℝ) := by
        simp only [cost, hzzeq]
        rw [← Finset.sum_coe_sort F (fun e => pairCost c e * (zF e : ℝ))]
        apply sum_congr rfl
        intro e _
        simp only [zF, dif_pos e.2]
      have hJF : J ⊆ F := filter_subset _ _
      have hle : ∑ e ∈ J, pairCost c e ≤ ∑ e ∈ F, pairCost c e * (zF e : ℝ) := by
        calc ∑ e ∈ J, pairCost c e ≤ ∑ e ∈ J, pairCost c e * (zF e : ℝ) := by
              apply sum_le_sum
              intro e he
              have hodd := (mem_filter.mp he).2
              have h1 : (1 : ℤ) ≤ zF e := by
                rcases hodd with ⟨k, hk⟩
                have := hzF0 e
                omega
              have h1' : (1 : ℝ) ≤ (zF e : ℝ) := by exact_mod_cast h1
              have := hc e (hJF he)
              nlinarith
          _ ≤ ∑ e ∈ F, pairCost c e * (zF e : ℝ) := by
              apply sum_le_sum_of_subset_of_nonneg hJF
              intro e he _
              exact mul_nonneg (hc e he) (by exact_mod_cast hzF0 e)
      rw [← hcost_y]
      linarith
  · -- an `O`-join meets every odd cut
    intro J hJ
    have hJF : J ⊆ F := by
      intro e he
      have := hJ.1 (Finset.mem_coe.mpr he)
      rw [hedge] at this; exact this
    have hJd : ∀ e ∈ J, ¬ e.IsDiag := fun e he => hloop e (hJF he)
    refine ⟨fun e _ => by show (0 : ℝ) ≤ (if e ∈ J then (1 : ℝ) else 0); split_ifs <;> norm_num, ?_⟩
    intro S hS
    have hpar : S.filter (fun v => Odd (J.filter (fun e => v ∈ e)).card) = S ∩ O := by
      ext v
      simp only [mem_filter, mem_inter]
      have := hJ.2 v
      unfold MetricGenerators.FewComponents.edgeDeg at this
      rw [this]
    have hodd := (odd_card_iff_odd_cross J hJd S).mp (by rw [hpar]; exact hS)
    have hpos : 0 < (J.filter (edgeCrosses S)).card := hodd.pos
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hsub : J.filter (edgeCrosses S) ⊆ (cutEdges F S).filter (fun e => e ∈ J) := by
      intro e he
      simp only [mem_filter, cutEdges] at he ⊢
      exact ⟨⟨hJF he.1, he.2⟩, he.1⟩
    have := card_le_card hsub
    have h1 : (1 : ℝ) ≤ ((J.filter (edgeCrosses S)).card : ℝ) := by exact_mod_cast hpos
    have h2 : ((J.filter (edgeCrosses S)).card : ℝ) ≤
        (((cutEdges F S).filter (fun e => e ∈ J)).card : ℝ) := by exact_mod_cast this
    linarith
