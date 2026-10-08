-- Prove2me | solution 1 for MatousekLP.Scheduling.rounding_makespan_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T00:31:12.905365+00:00
-- url     : https://prove2.me/submissions/a555155a-fdfa-4656-8195-67d54f190a1f

import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_MatousekLP_Scheduling_LPRelaxation
import Mathlib

open MatousekLP.Scheduling

private theorem support_subgraph_edges_le {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (hd : ∀ i j, 0 < d i j) (T t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ)
    (hopt : LPROptimal d T t x) (hA : Assumption831 d T x)
    (M' : Finset (Fin m)) (J' : Finset (Fin n)) (E' : Finset (Fin m × Fin n))
    (hE'E : E' ⊆ supportEdges x) (hE'V : ∀ e ∈ E', e.1 ∈ M' ∧ e.2 ∈ J') :
    E'.card ≤ M'.card + J'.card := by
  classical
  have hpos : ∀ e ∈ E', 0 < x e.1 e.2 := fun e he => by
    have := hE'E he; simpa [supportEdges] using this
  -- the columns indexed by `E'`
  have hinj : Function.Injective (fun e : E' =>
      (⟨e.1, (hpos e.1 e.2).ne'⟩ : {c : Fin m × Fin n // x c.1 c.2 ≠ 0})) := by
    intro a b h; apply Subtype.ext; have := congrArg Subtype.val h; simpa using this
  have hind := hA.comp _ hinj
  set col : E' → (Fin m ⊕ Fin n ⊕ {p : Fin m × Fin n // T < d p.1 p.2}) → ℝ :=
    fun e r => constraintMatrix d T r e.1 with hcol
  replace hind : LinearIndependent ℝ col := hind
  -- they live in the coordinate subspace of the rows of `M'` and `J'`
  set Rows : Finset (Fin m ⊕ Fin n ⊕ {p : Fin m × Fin n // T < d p.1 p.2}) := M'.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    J'.map ⟨fun j => Sum.inr (Sum.inl j), fun a b h => by simpa using h⟩
  set W := Submodule.span ℝ (Set.range fun r : Rows => (Pi.single (r : Fin m ⊕ Fin n ⊕ {p : Fin m × Fin n // T < d p.1 p.2}) (1 : ℝ) : (Fin m ⊕ Fin n ⊕ {p : Fin m × Fin n // T < d p.1 p.2}) → ℝ))
  have hcolW : ∀ e : E', col e ∈ W := by
    intro e
    have hzero : ∀ r : Fin m ⊕ Fin n ⊕ {p : Fin m × Fin n // T < d p.1 p.2}, r ∉ Rows → col e r = 0 := by
      intro r hr
      rcases r with i | j | p
      · simp only [col, constraintMatrix, Matrix.of_apply]
        split_ifs with h
        · exact absurd (by simp [Rows, ← h, (hE'V e.1 e.2).1]) hr
        · rfl
      · simp only [col, constraintMatrix, Matrix.of_apply]
        split_ifs with h
        · exact absurd (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨_, (hE'V e.1 e.2).2, by rw [← h]; rfl⟩)) hr
        · rfl
      · simp only [col, constraintMatrix, Matrix.of_apply]
        split_ifs with h
        · have := hopt.1.2.2.2 p.1.1 p.1.2 p.2
          rw [← h] at this
          exact absurd this (hpos e.1 e.2).ne'
        · rfl
    have : col e = ∑ r : Rows, col e r • (Pi.single (r : Fin m ⊕ Fin n ⊕ {p : Fin m × Fin n // T < d p.1 p.2}) (1 : ℝ) : (Fin m ⊕ Fin n ⊕ {p : Fin m × Fin n // T < d p.1 p.2}) → ℝ) := by
      funext r'
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      by_cases hr' : r' ∈ Rows
      · rw [Finset.sum_eq_single ⟨r', hr'⟩ (fun b _ hb => if_neg (fun h => hb (Subtype.ext h.symm)))
          (by simp)]
        simp
      · rw [hzero r' hr', Finset.sum_eq_zero]
        intro b _
        rw [if_neg]; rintro rfl; exact hr' b.2
    rw [this]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range col)) = E'.card := by
    rw [finrank_span_eq_card hind]; simp
  have h2 : Submodule.span ℝ (Set.range col) ≤ W := by
    rw [Submodule.span_le]; rintro _ ⟨e, rfl⟩; exact hcolW e
  have h3 : Module.finrank ℝ W ≤ Rows.card := by
    have := finrank_range_le_card (R := ℝ) (fun r : Rows => (Pi.single (r : Fin m ⊕ Fin n ⊕ {p : Fin m × Fin n // T < d p.1 p.2}) (1 : ℝ) : (Fin m ⊕ Fin n ⊕ {p : Fin m × Fin n // T < d p.1 p.2}) → ℝ))
    simpa [Set.finrank] using this
  have h4 : Rows.card ≤ M'.card + J'.card := by
    refine (Finset.card_union_le _ _).trans ?_
    simp
  have := Submodule.finrank_mono h2
  omega

private theorem match_fractional {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (hd : ∀ i j, 0 < d i j) (T t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ)
    (ho : LPROptimal d T t x) (ha : Assumption831 d T x) :
    ∃ f : {j : Fin n // 2 ≤ (Finset.univ.filter (fun i => 0 < x i j)).card} → Fin m,
      Function.Injective f ∧ ∀ j, 0 < x (f j) j := by
  classical
  let N := fun j : Fin n => Finset.univ.filter (fun i => 0 < x i j)
  let F := {j : Fin n // 2 ≤ (N j).card}
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun j : F => N j)).mp (by
      intro s
      let J := s.image (fun j : F => j.val)
      let M := s.biUnion (fun j : F => N j)
      let E := J.biUnion (fun j => (N j).image (fun i => (i,j)))
      have hE : E ⊆ supportEdges x := by
        intro e he
        obtain ⟨j, _, he⟩ := Finset.mem_biUnion.mp he
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
        simpa [supportEdges, N] using hi
      have hv : ∀ e ∈ E, e.1 ∈ M ∧ e.2 ∈ J := by
        intro e he
        obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
        exact ⟨Finset.mem_biUnion.mpr ⟨k, hk, hi⟩, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩
      have hc := support_subgraph_edges_le d hd T t x ho ha M J E hE hv
      have hcard : J.card = s.card := Finset.card_image_of_injective _ Subtype.val_injective
      have hEc : E.card = ∑ j ∈ J, (N j).card := by
        rw [Finset.card_biUnion]
        · apply Finset.sum_congr rfl
          intro j hj
          exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)
        · intro a ha b hb hab
          apply Finset.disjoint_left.mpr
          intro e he he'
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
          obtain ⟨k, _, h⟩ := Finset.mem_image.mp he'
          exact hab (Prod.mk.inj h).2.symm
      have hlow : 2 * J.card ≤ E.card := by
        rw [hEc]
        calc
          2 * J.card = ∑ _j ∈ J, 2 := by simp [Nat.mul_comm]
          _ ≤ ∑ j ∈ J, (N j).card := by
            apply Finset.sum_le_sum
            intro j hj
            obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
            exact k.property
      dsimp [M] at hc
      omega)
  exact ⟨f, hf, fun j => by simpa [N] using hmem j⟩

theorem solution {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (hd : ∀ i j, 0 < d i j) (T : ℝ) (hT : 0 ≤ T) (tstar : ℝ)
    (xstar : Matrix (Fin m) (Fin n) ℝ)
    (hopt : LPROptimal d T tstar xstar) (hA : Assumption831 d T xstar) :
    ∃ σ : Fin n → Fin m, (∀ j, 0 < xstar (σ j) j) ∧ makespan d σ ≤ tstar + T := by
  classical
  let N := fun j : Fin n => Finset.univ.filter (fun i => 0 < xstar i j)
  have hn : ∀ j, (N j).Nonempty := by
    intro j
    by_contra h
    have hz : ∀ i, xstar i j = 0 := by
      intro i
      have hh : ¬ 0 < xstar i j := by
        intro hi
        exact h ⟨i, by simpa [N] using hi⟩
      linarith [hopt.1.2.2.1 i j]
    have := hopt.1.1 j
    simp [hz] at this
  obtain ⟨f, hf, hp⟩ := match_fractional d hd T tstar xstar hopt hA
  let σ : Fin n → Fin m := fun j =>
    if h : 2 ≤ (N j).card then f ⟨j,h⟩ else (hn j).choose
  have hs : ∀ j, 0 < xstar (σ j) j := by
    intro j
    dsimp [σ]
    split_ifs with h
    · exact hp ⟨j,h⟩
    · have := (hn j).choose_spec
      simpa [N] using this
  have hone : ∀ j, ¬ 2 ≤ (N j).card → xstar (σ j) j = 1 := by
    intro j hj
    have hcard : (N j).card = 1 := by have := (hn j).card_pos; omega
    have hsingle : N j = {σ j} := by
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
      have hm : σ j ∈ N j := by simpa [N] using hs j
      rw [hi, Finset.mem_singleton] at hm
      simpa [hm] using hi
    have hz : ∀ i, i ≠ σ j → xstar i j = 0 := by
      intro i hi
      have hn' : ¬ 0 < xstar i j := by
        intro hp'
        have : i ∈ N j := by simpa [N] using hp'
        simpa [hsingle, hi] using this
      linarith [hopt.1.2.2.1 i j]
    have := hopt.1.1 j
    rwa [Finset.sum_eq_single (σ j) (fun i _ hi => hz i hi) (by simp)] at this
  have hload : ∀ i, load d σ i ≤ tstar + T := by
    intro i
    let A := Finset.univ.filter (fun j => σ j = i ∧ ¬ 2 ≤ (N j).card)
    let B := Finset.univ.filter (fun j => σ j = i ∧ 2 ≤ (N j).card)
    have hAc : (∑ j ∈ A, d i j) ≤ tstar := by
      calc
        _ = ∑ j ∈ A, d i j * xstar i j := by
          apply Finset.sum_congr rfl
          intro j hj
          obtain ⟨_, hji, hsmall⟩ := Finset.mem_filter.mp hj
          rw [← hji, hone j hsmall, mul_one]
        _ ≤ ∑ j, d i j * xstar i j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ =>
            mul_nonneg (hd i j).le (hopt.1.2.2.1 i j))
        _ ≤ tstar := hopt.1.2.1 i
    have hBc : B.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨_, hai, ha'⟩ := Finset.mem_filter.mp ha
      obtain ⟨_, hbi, hb'⟩ := Finset.mem_filter.mp hb
      have he : f ⟨a,ha'⟩ = f ⟨b,hb'⟩ := by
        simpa [σ, ha', hb'] using hai.trans hbi.symm
      exact congrArg Subtype.val (hf he)
    have hBc' : (∑ j ∈ B, d i j) ≤ T := by
      calc
        _ ≤ ∑ _j ∈ B, T := by
          apply Finset.sum_le_sum
          intro j hj
          have hji := (Finset.mem_filter.mp hj).2.1
          have hpos : 0 < xstar i j := hji ▸ hs j
          by_contra h
          have := hopt.1.2.2.2 i j (lt_of_not_ge h)
          linarith
        _ = (B.card : ℝ) * T := by simp
        _ ≤ T := by
          have : (B.card : ℝ) ≤ 1 := by exact_mod_cast hBc
          nlinarith
    have hsplit : load d σ i = (∑ j ∈ A, d i j) + ∑ j ∈ B, d i j := by
      simp only [load, A, B, Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : σ j = i <;> by_cases hsmall : 2 ≤ (N j).card <;> simp [hji, hsmall]
    rw [hsplit]
    linarith
  have hm : Nonempty (Fin m) := by
    by_contra h
    have hempty : IsEmpty (Fin m) := ⟨fun i => h ⟨i⟩⟩
    letI := hempty
    have hh : LPRFeasible d T (tstar - 1) xstar :=
      ⟨hopt.1.1, fun i => isEmptyElim i, hopt.1.2.2⟩
    have := hopt.2 (tstar - 1) xstar hh
    linarith
  letI := hm
  exact ⟨σ, hs, ciSup_le hload⟩
