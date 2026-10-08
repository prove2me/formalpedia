-- Prove2me | solution 1 for MatousekLP.Scheduling.support_subgraph_edges_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:06:58.824987+00:00
-- url     : https://prove2.me/submissions/cf8df7dc-5f99-4fc2-83bb-e348bb6ac911

import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_MatousekLP_Scheduling_LPRelaxation
import Mathlib

open MatousekLP.Scheduling

theorem solution {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
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
