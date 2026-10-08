-- Prove2me | solution 1 for MatousekLP.Integrality.incidenceMatrix_totallyUnimodular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:26:18.873186+00:00
-- url     : https://prove2.me/submissions/67f320dd-e543-4fb5-bd9a-2ffc18fba519

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph
import Definitions.Def_MatousekLP_Integrality_IncidenceMatrix

set_option autoImplicit false

namespace B74fc86dAux

lemma signCast_mul {a b : ℝ} (ha : a ∈ Set.range (SignType.cast : SignType → ℝ))
    (hb : b ∈ Set.range (SignType.cast : SignType → ℝ)) :
    a * b ∈ Set.range (SignType.cast : SignType → ℝ) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  exact ⟨s * t, by simp [SignType.coe_mul]⟩

lemma signCast_negOnePow (n : ℕ) :
    ((-1 : ℝ) ^ n) ∈ Set.range (SignType.cast : SignType → ℝ) := by
  rcases neg_one_pow_eq_or ℝ n with h | h
  · exact ⟨1, by simp [h]⟩
  · exact ⟨-1, by simp [h]⟩

theorem tu_of {m n : Type*} (A : Matrix m n ℝ)
    (hent : ∀ i j, A i j ∈ Set.range (SignType.cast : SignType → ℝ))
    (key : ∀ k (f : Fin k → m) (g : Fin k → n), f.Injective → g.Injective → 0 < k →
      (∃ j i, ∀ i', i' ≠ i → A (f i') (g j) = 0) ∨
      ∃ v : Fin k → ℝ, v ≠ 0 ∧ Matrix.vecMul v (A.submatrix f g) = 0) :
    A.IsTotallyUnimodular := by
  intro k
  induction k with
  | zero => intro f g _ _; exact ⟨1, by simp⟩
  | succ k ih =>
    intro f g hf hg
    rcases key (k+1) f g hf hg (Nat.succ_pos k) with ⟨j, i, hcol⟩ | ⟨v, hv0, hv⟩
    · rw [Matrix.det_succ_column _ j, Finset.sum_eq_single i]
      · refine signCast_mul (signCast_mul (signCast_negOnePow _) ?_) ?_
        · exact hent _ _
        · have := ih (f ∘ i.succAbove) (g ∘ j.succAbove)
            (hf.comp (Fin.succAbove_right_injective))
            (hg.comp (Fin.succAbove_right_injective))
          simpa [Matrix.submatrix_submatrix] using this
      · intro b _ hb
        simp [hcol b hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    · have : (A.submatrix f g).det = 0 :=
        (Matrix.exists_vecMul_eq_zero_iff).1 ⟨v, hv0, hv⟩
      exact ⟨0, by simp [this]⟩

end B74fc86dAux

open MatousekLP.Integrality in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBipartite G) :
    (incidenceMatrix G).IsTotallyUnimodular := by
  obtain ⟨X, Y, hdisj, hcov, hadj⟩ := hG
  apply B74fc86dAux.tu_of
  · intro i j
    by_cases h : i ∈ (j : Sym2 V)
    · exact ⟨1, by simp [incidenceMatrix, h]⟩
    · exact ⟨0, by simp [incidenceMatrix, h]⟩
  · intro k f g hf hg hk
    by_cases h : ∃ j, ∀ i i', incidenceMatrix G (f i) (g j) ≠ 0 →
        incidenceMatrix G (f i') (g j) ≠ 0 → i = i'
    · left
      obtain ⟨j, hj⟩ := h
      by_cases hz : ∃ i, incidenceMatrix G (f i) (g j) ≠ 0
      · obtain ⟨i, hi⟩ := hz
        refine ⟨j, i, fun i' hi' => ?_⟩
        by_contra hne
        exact hi' (hj i i' hi hne).symm
      · push_neg at hz
        exact ⟨j, ⟨0, hk⟩, fun i' _ => hz i'⟩
    · right
      push_neg at h
      refine ⟨fun l => if f l ∈ X then 1 else -1, ?_, ?_⟩
      · intro h0
        have := congrFun h0 ⟨0, hk⟩
        simp only [Pi.zero_apply] at this
        split_ifs at this <;> norm_num at this
      · funext j
        obtain ⟨i, i', hi, hi', hne⟩ := h j
        have hmi : f i ∈ (g j : Sym2 V) := by
          by_contra hc; exact hi (by simp [incidenceMatrix, hc])
        have hmi' : f i' ∈ (g j : Sym2 V) := by
          by_contra hc; exact hi' (by simp [incidenceMatrix, hc])
        have hfne : f i ≠ f i' := fun h => hne (hf h)
        have he : (g j : Sym2 V) = s(f i, f i') := (Sym2.mem_and_mem_iff hfne).1 ⟨hmi, hmi'⟩
        have hA : G.Adj (f i) (f i') := by
          have := (g j).2
          rw [he] at this
          exact this
        have hmem : ∀ l, f l ∈ (g j : Sym2 V) ↔ (l = i ∨ l = i') := by
          intro l
          rw [he, Sym2.mem_iff]
          constructor
          · rintro (h | h)
            · exact Or.inl (hf h)
            · exact Or.inr (hf h)
          · rintro (rfl | rfl)
            · exact Or.inl rfl
            · exact Or.inr rfl
        have hsum : ∀ l, (if f l ∈ X then (1:ℝ) else -1) *
            (if f l ∈ (g j : Sym2 V) then 1 else 0) =
            (if l = i then (if f i ∈ X then (1:ℝ) else -1) else 0) +
            (if l = i' then (if f i' ∈ X then (1:ℝ) else -1) else 0) := by
          intro l
          by_cases h1 : l = i
          · subst h1; simp [hmi, hne]
          · by_cases h2 : l = i'
            · subst h2; simp [hmi', h1]
            · have : f l ∉ (g j : Sym2 V) := by
                rw [hmem]; push_neg; exact ⟨h1, h2⟩
              simp [this, h1, h2]
        simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
        simp only [incidenceMatrix, Matrix.of_apply]
        rw [Finset.sum_congr rfl (fun l _ => hsum l), Finset.sum_add_distrib,
          Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true]
        rcases hadj _ _ hA with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · have : f i' ∉ X := fun h => Finset.disjoint_left.1 hdisj h hy
          simp [hx, this]
        · have : f i ∉ X := fun h => Finset.disjoint_left.1 hdisj h hy
          simp [hx, this]
