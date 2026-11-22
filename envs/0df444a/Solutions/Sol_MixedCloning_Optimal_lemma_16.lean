-- Prove2me | solution 1 for MixedCloning.Optimal.lemma_16
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:36:14.183364+00:00
-- url     : https://prove2.me/submissions/23214422-93a0-4fe6-9cc2-9a1a8910d3a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MixedCloning_Optimal_Schur
import Theorems.Thm_MixedCloning_Optimal_hook_content

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

namespace L16F

/-! ### The content factor `x ↦ (r+x)/(d+x)` -/

lemma cfrac_nonneg {r d x : ℝ} (hrd : r ≤ d) (hx : 0 < r + x) : 0 ≤ (r + x) / (d + x) :=
  div_nonneg hx.le (by linarith)

lemma cfrac_le_one {r d x : ℝ} (hrd : r ≤ d) (hx : 0 < r + x) : (r + x) / (d + x) ≤ 1 := by
  rw [div_le_one (by linarith)]; linarith

lemma cfrac_mono {r d x y : ℝ} (hrd : r ≤ d) (hx : 0 < r + x) (hxy : x ≤ y) :
    (r + x) / (d + x) ≤ (r + y) / (d + y) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma content_cast (c : ℕ × ℕ) : (content c : ℝ) = (c.2 : ℝ) - c.1 := by
  simp [content]

lemma content_pos_of_row {t : ℕ} (c : ℕ × ℕ) (hc : c.1 < t) : 0 < (t : ℝ) + (content c : ℝ) := by
  rw [content_cast]
  have h1 : (c.1 : ℝ) < t := by exact_mod_cast hc
  have h2 : (0 : ℝ) ≤ c.2 := Nat.cast_nonneg _
  linarith

lemma row_lt_height (A : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ A.cells) : c.1 < height A := by
  obtain ⟨i, j⟩ := c
  have : (i, 0) ∈ A := A.up_left_mem le_rfl (Nat.zero_le j) hc
  exact YoungDiagram.mem_iff_lt_colLen.mp this

/-! ### Zero count for too-tall diagrams -/

lemma card_zero_of_isEmpty {α : Type*} (inst : Fintype α) (h : IsEmpty α) :
    @Fintype.card α inst = 0 :=
  @Fintype.card_eq_zero α inst h

lemma schurCount_eq_zero (L : YoungDiagram) (t : ℕ) (h : t < height L) : schurCount L t = 0 := by
  unfold schurCount
  refine card_zero_of_isEmpty _ ⟨fun ⟨T, hT⟩ => ?_⟩
  have hmem : ∀ i, i ≤ t → (i, 0) ∈ L.cells := fun i hi =>
    YoungDiagram.mem_iff_lt_colLen.mpr (by unfold height at h; omega)
  let g : Fin (t+1) → Fin t := fun i => T ⟨(i.val, 0), hmem i.val (by omega)⟩
  have hg : StrictMono g := by
    intro a b hab
    exact hT.2 _ _ rfl hab
  have := Fintype.card_le_of_injective g hg.injective
  simp at this

lemma ratio_eq_zero (L : YoungDiagram) (t d : ℕ) (h : t < height L) : ratio L t d = 0 := by
  unfold ratio
  rw [schurCount_eq_zero L t h]
  simp

lemma ratio_nonneg (L : YoungDiagram) (t d : ℕ) : 0 ≤ ratio L t d :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ### Ratios as content products (hook lengths cancel) -/

lemma hook_ne_zero (L : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ L.cells) : hook L c ≠ 0 := by
  unfold hook
  exact Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨hc, Or.inl ⟨rfl, le_rfl⟩⟩)

lemma ratio_eq_prod (L : YoungDiagram) (t d : ℕ) (ht : height L ≤ t) (htd : t ≤ d) :
    ratio L t d = ∏ c ∈ L.cells, ((t : ℝ) + content c) / ((d : ℝ) + content c) := by
  have h1 := (MixedCloning.Optimal.hook_content t L ht).2
  have h2 := (MixedCloning.Optimal.hook_content d L (ht.trans htd)).2
  unfold ratio
  rw [h1, h2, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun c hc => ?_
  have hh : (hook L c : ℝ) ≠ 0 := by exact_mod_cast hook_ne_zero L c hc
  exact div_div_div_cancel_right₀ hh _ _

/-! ### The key combinatorial bound -/

/-- Content factor of a cell. -/
def F (r d : ℕ) (c : ℕ × ℕ) : ℝ := ((r : ℝ) + content c) / ((d : ℝ) + content c)

/-- The `j`-th first-row factor. -/
def G (r d l j : ℕ) : ℝ := ((r : ℝ) + l + j) / ((d : ℝ) + l + j)

lemma G_nonneg (r d l j : ℕ) : 0 ≤ G r d l j := by
  unfold G; positivity

/-- If `S` is a finite set of cells in rows `< r`, closed under "move to the first row and then
left, but not past column `l`", then the product of the content factors over `S` is at most the
product of the first `k` first-row factors, for every `k ≤ |S|`. -/
lemma key (r d l : ℕ) (hrd : r ≤ d) :
    ∀ S : Finset (ℕ × ℕ), (∀ c ∈ S, c.1 < r) →
      (∀ c ∈ S, ∀ j, l ≤ j → j ≤ c.2 → ((0 : ℕ), j) ∈ S) →
      ∀ k ≤ S.card, ∏ c ∈ S, F r d c ≤ ∏ j ∈ Finset.range k, G r d l j := by
  have hrd' : (r : ℝ) ≤ d := by exact_mod_cast hrd
  intro S
  induction S using Finset.induction_on_max_value (fun c : ℕ × ℕ => c.1 + c.2) with
  | empty =>
    intro _ _ k hk
    simp only [Finset.card_empty, Nat.le_zero] at hk
    subst hk
    simp
  | insert a s ha hmax ih =>
    intro hrow hfill k hk
    rw [Finset.card_insert_of_notMem ha] at hk
    rw [Finset.prod_insert ha]
    have hrow' : ∀ c ∈ s, c.1 < r := fun c hc => hrow c (Finset.mem_insert_of_mem hc)
    have hfill' : ∀ c ∈ s, ∀ j, l ≤ j → j ≤ c.2 → ((0 : ℕ), j) ∈ s := by
      intro c hc j hlj hjc
      rcases Finset.mem_insert.mp (hfill c (Finset.mem_insert_of_mem hc) j hlj hjc) with h | h
      · exfalso
        have hm : c.1 + c.2 ≤ a.1 + a.2 := hmax c hc
        have h1 : a.1 = 0 := by rw [← h]
        have h2 : a.2 = j := by rw [← h]
        have hca : c = a := Prod.ext (by omega) (by omega)
        exact ha (hca ▸ hc)
      · exact h
    have ih' := ih hrow' hfill'
    -- the removed cell has column at most `l + |s|`
    have ha2 : a.2 ≤ l + s.card := by
      by_cases hla : l ≤ a.2
      · have hsub : (Finset.Icc l a.2).image (fun j => ((0 : ℕ), j)) ⊆ insert a s := by
          intro x hx
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
          rw [Finset.mem_Icc] at hj
          exact hfill a (Finset.mem_insert_self a s) j hj.1 hj.2
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h), Nat.card_Icc,
          Finset.card_insert_of_notMem ha] at hcard
        omega
      · omega
    have hx : 0 < (r : ℝ) + content a := content_pos_of_row a (hrow a (Finset.mem_insert_self a s))
    have hFa0 : 0 ≤ F r d a := cfrac_nonneg hrd' hx
    have hFa1 : F r d a ≤ 1 := cfrac_le_one hrd' hx
    have hprod0 : 0 ≤ ∏ c ∈ s, F r d c := Finset.prod_nonneg fun c hc =>
      cfrac_nonneg hrd' (content_pos_of_row c (hrow' c hc))
    rcases Nat.lt_or_ge k (s.card + 1) with hk' | hk'
    · calc F r d a * ∏ c ∈ s, F r d c ≤ 1 * ∏ c ∈ s, F r d c :=
            mul_le_mul_of_nonneg_right hFa1 hprod0
        _ = ∏ c ∈ s, F r d c := one_mul _
        _ ≤ ∏ j ∈ Finset.range k, G r d l j := ih' k (by omega)
    · have hk2 : k = s.card + 1 := by omega
      subst hk2
      rw [Finset.prod_range_succ, mul_comm (∏ j ∈ Finset.range s.card, G r d l j)]
      refine mul_le_mul ?_ (ih' s.card le_rfl) hprod0 (G_nonneg _ _ _ _)
      have hxle : (content a : ℝ) ≤ (l : ℝ) + (s.card : ℝ) := by
        rw [content_cast]
        have h1 : (a.2 : ℝ) ≤ l + s.card := by exact_mod_cast ha2
        have h2 : (0 : ℝ) ≤ a.1 := Nat.cast_nonneg _
        linarith
      have := cfrac_mono hrd' hx hxle
      unfold F G
      rw [add_assoc (r : ℝ), add_assoc (d : ℝ)]
      exact this

/-! ### `addTop` -/

lemma mem_addTop (L : YoungDiagram) (k : ℕ) (c : ℕ × ℕ) :
    c ∈ (addTop L k).cells ↔ c ∈ L.cells ∨ (c.1 = 0 ∧ c.2 < L.rowLen 0 + k) := by
  rcases c with ⟨i, j⟩
  simp only [addTop, YoungDiagram.mem_cells, YoungDiagram.mem_sup, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · right
      simp only [List.length_singleton] at h1
      have hi : i = 0 := by omega
      subst hi
      exact ⟨rfl, by simpa using h2⟩
  · rintro (h | ⟨rfl, h2⟩)
    · exact Or.inl h
    · right
      exact ⟨by simp, by simpa using h2⟩

lemma height_addTop_le (L : YoungDiagram) (k r : ℕ) (hr : 1 ≤ r) (hL : height L ≤ r) :
    height (addTop L k) ≤ r := by
  by_contra h
  push_neg at h
  have hmem : (r, 0) ∈ (addTop L k).cells := YoungDiagram.mem_iff_lt_colLen.mpr h
  rcases (mem_addTop L k (r, 0)).mp hmem with h1 | ⟨h1, _⟩
  · have := YoungDiagram.mem_iff_lt_colLen.mp h1
    unfold height at hL
    omega
  · simp only at h1
    omega

/-- The new cells of `addTop L k`. -/
def newCells (L : YoungDiagram) (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range k).image fun j => ((0 : ℕ), L.rowLen 0 + j)

lemma newCells_inj (L : YoungDiagram) :
    Function.Injective fun j : ℕ => ((0 : ℕ), L.rowLen 0 + j) := by
  intro x y h
  simp only [Prod.mk.injEq, true_and] at h
  omega

lemma addTop_cells (L : YoungDiagram) (k : ℕ) :
    (addTop L k).cells = L.cells ∪ newCells L k := by
  ext ⟨i, j⟩
  rw [mem_addTop, Finset.mem_union, newCells, Finset.mem_image]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · simp only at h1 h2
      subst h1
      by_cases hj : j < L.rowLen 0
      · exact Or.inl (YoungDiagram.mem_iff_lt_rowLen.mpr hj)
      · right
        refine ⟨j - L.rowLen 0, Finset.mem_range.mpr (by omega), ?_⟩
        show ((0 : ℕ), L.rowLen 0 + (j - L.rowLen 0)) = (0, j)
        exact Prod.ext rfl (show L.rowLen 0 + (j - L.rowLen 0) = j by omega)
  · rintro (h | ⟨x, hx, hxe⟩)
    · exact Or.inl h
    · right
      rw [Finset.mem_range] at hx
      have e1 : (0 : ℕ) = i := congrArg Prod.fst hxe
      have e2 : L.rowLen 0 + x = j := congrArg Prod.snd hxe
      exact ⟨e1.symm, by omega⟩

lemma addTop_disj (L : YoungDiagram) (k : ℕ) : Disjoint L.cells (newCells L k) := by
  rw [Finset.disjoint_left]
  intro c hc hc'
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc'
  have := YoungDiagram.mem_iff_lt_rowLen.mp hc
  omega

lemma addTop_card (L : YoungDiagram) (k : ℕ) : (addTop L k).card = L.card + k := by
  show (addTop L k).cells.card = L.cells.card + k
  rw [addTop_cells, Finset.card_union_of_disjoint (addTop_disj L k), newCells,
    Finset.card_image_of_injective _ (newCells_inj L), Finset.card_range]

lemma addTop_prod (r d : ℕ) (L : YoungDiagram) (k : ℕ) :
    ∏ c ∈ (addTop L k).cells, F r d c =
      (∏ c ∈ L.cells, F r d c) * ∏ j ∈ Finset.range k, G r d (L.rowLen 0) j := by
  rw [addTop_cells, Finset.prod_union (addTop_disj L k), newCells,
    Finset.prod_image fun x _ y _ h => newCells_inj L h]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold F G
  rw [content_cast]
  push_cast
  ring_nf

lemma sup_addTop (L : YoungDiagram) (k : ℕ) : L ⊔ addTop L k = addTop L k :=
  sup_left_idem _ _

lemma extraProduct_eq (d r k : ℕ) (L : YoungDiagram) :
    extraProduct d r k L = ∏ j ∈ Finset.range k, G r d (L.rowLen 0) j := by
  unfold extraProduct G
  exact Fin.prod_univ_eq_prod_range (fun j => ((r : ℝ) + L.rowLen 0 + j) / ((d : ℝ) + L.rowLen 0 + j)) k

/-! ### Comparison with an arbitrary competitor -/

lemma part2_core (r d k : ℕ) (hrd : r ≤ d) (L A : YoungDiagram) (hLA : L ≤ A)
    (hA : height A ≤ r) (hcard : L.card + k ≤ A.card) :
    ∏ c ∈ A.cells, F r d c ≤
      (∏ c ∈ L.cells, F r d c) * ∏ j ∈ Finset.range k, G r d (L.rowLen 0) j := by
  have hrd' : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hsub : L.cells ⊆ A.cells := YoungDiagram.cells_subset_iff.mpr hLA
  rw [← Finset.prod_sdiff hsub]
  have hrowA : ∀ c ∈ A.cells, c.1 < r := fun c hc => (row_lt_height A c hc).trans_le hA
  have hS : ∏ c ∈ A.cells \ L.cells, F r d c ≤ ∏ j ∈ Finset.range k, G r d (L.rowLen 0) j := by
    refine key r d (L.rowLen 0) hrd (A.cells \ L.cells) ?_ ?_ k ?_
    · intro c hc
      exact hrowA c (Finset.mem_sdiff.mp hc).1
    · intro c hc j hlj hjc
      have hcA := (Finset.mem_sdiff.mp hc).1
      rw [Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · obtain ⟨i, j'⟩ := c
        exact A.up_left_mem (Nat.zero_le i) hjc hcA
      · intro h0
        have := YoungDiagram.mem_iff_lt_rowLen.mp h0
        omega
    · rw [Finset.card_sdiff_of_subset hsub]
      show k ≤ A.card - L.card
      omega
  have hL0 : 0 ≤ ∏ c ∈ L.cells, F r d c := Finset.prod_nonneg fun c hc =>
    cfrac_nonneg hrd' (content_pos_of_row c (hrowA c (hsub hc)))
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hS hL0

end L16F

open L16F

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (d r n k : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (L : YoungDiagram) (hsize : L.card = n) (hL : height L ≤ r) :
    ((addTop L k).card = n+k ∧ height (addTop L k) ≤ d) ∧
    (∀ M : YoungDiagram, M.card = n+k → height M ≤ d →
      ratio (L ⊔ M) r d ≤ ratio (L ⊔ addTop L k) r d) ∧
    ratio (L ⊔ addTop L k) r d = ratio L r d * extraProduct d r k L := by
  have hA : height (addTop L k) ≤ r := height_addTop_le L k r hr hL
  have heq : ratio (L ⊔ addTop L k) r d = ratio L r d * extraProduct d r k L := by
    rw [sup_addTop, ratio_eq_prod _ r d hA hrd, ratio_eq_prod L r d hL hrd, extraProduct_eq]
    exact addTop_prod r d L k
  refine ⟨⟨by rw [addTop_card, hsize], hA.trans hrd⟩, ?_, heq⟩
  intro M hM _
  by_cases hh : height (L ⊔ M) ≤ r
  · rw [heq, ratio_eq_prod _ r d hh hrd, ratio_eq_prod L r d hL hrd, extraProduct_eq]
    refine part2_core r d k hrd L (L ⊔ M) le_sup_left hh ?_
    have hMle : M.card ≤ (L ⊔ M).card :=
      Finset.card_le_card (YoungDiagram.cells_subset_iff.mpr le_sup_right)
    omega
  · push_neg at hh
    rw [ratio_eq_zero _ r d hh]
    exact ratio_nonneg _ r d
