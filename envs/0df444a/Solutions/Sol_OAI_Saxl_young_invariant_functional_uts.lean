-- Prove2me | solution 1 for OAI.Saxl.young_invariant_functional_uts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:13:33.314186+00:00
-- url     : https://prove2.me/submissions/8326fcb9-9c8f-44c4-b870-65a722024a0e

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_Saxl_pieri_strip_surjective_uts

section
-- module Solutions.OAIQ259_US.Saxl_StripExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma restrictPerm_apply {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin n))
    (hg : ∀ x, g x ∈ Set.range i ↔ x ∈ Set.range i) (k : Fin a) :
    i (restrictPerm i g hg k) = g (i k) := by
  change ((Equiv.ofInjective i i.injective)
    ((Equiv.ofInjective i i.injective).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma tableauInclusion_trans {a b n : ℕ} {ν η μ : YoungDiagram}
    (s : Tableau a ν) (u : Tableau b η) (t : Tableau n μ)
    (h₁ : ν ≤ η) (h₂ : η ≤ μ) (k : Fin a) :
    tableauInclusion u t h₂ (tableauInclusion s u h₁ k) =
      tableauInclusion s t (h₁.trans h₂) k := by
  change t.symm ⟨(u (u.symm ⟨(s k).val, _⟩)).val, _⟩ = t.symm ⟨(s k).val, _⟩
  simp only [Equiv.apply_symm_apply]

lemma extendColor_apply {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (x : Fin a) : extendColor i c q (i x) = c x := by
  classical
  unfold extendColor
  rw [dite_eq_left ⟨x,rfl⟩]
  congr 1
  exact (Equiv.ofInjective i i.injective).symm_apply_apply x

lemma extendColor_mem {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) (x : Fin n) :
    extendColor i c (q+1) x ≤ q ↔ x ∈ Set.range i := by
  classical
  unfold extendColor
  split_ifs with h
  · exact iff_of_true (hc _) h
  · simp [h]

lemma extendColor_le {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) (x : Fin n) : extendColor i c (q+1) x ≤ q+1 := by
  classical
  unfold extendColor
  split_ifs
  · exact (hc _).trans (Nat.le_succ q)
  · exact le_rfl

lemma extendColor_count_old {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q j : ℕ)
    (hj : j ≠ q) :
    (Finset.univ.filter (fun x => extendColor i c q x = j)).card =
      (Finset.univ.filter (fun x => c x = j)).card := by
  classical
  symm
  apply Finset.card_bij (fun x _ => i x)
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, extendColor_apply] using hx
  · intro x hx y hy hxy
    exact i.injective hxy
  · intro y hy
    have hyj := (Finset.mem_filter.mp hy).2
    have hym : y ∈ Set.range i := by
      by_contra hn
      simp only [extendColor, dite_eq_right hn] at hyj
      exact hj hyj.symm
    obtain ⟨x,rfl⟩ := hym
    refine ⟨x, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, extendColor_apply] using hyj

lemma extendColor_count_new {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) :
    (Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1)).card = n-a := by
  classical
  have he : Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1) =
      Finset.univ \ Finset.univ.map i := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_map]
    change extendColor i c (q+1) x = q+1 ↔ ¬ x ∈ Set.range i
    rw [← extendColor_mem i c q hc x]
    have hl := extendColor_le i c q hc x
    omega
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SizedStrips
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma tableauInclusion_self {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (k : Fin n) :
    tableauInclusion t t le_rfl k = k := by
  change t.symm (t k) = k
  exact t.symm_apply_apply k

/- Iterated positive Pieri, with an explicit coloring of the added strips.
The map is surjective and equivariant for all permutations preserving each
strip, not just for the smaller symmetric group. -/
theorem stripChain_restriction {bs ν μ} (hs : SizedStripChain bs ν μ) :
    ∃ (c : Fin μ.card → ℕ) (F : Specht (shapeTableau μ) →ₗ[ℂ] Specht (shapeTableau ν)),
      Function.Surjective F ∧
      (∀ i, c i ≤ bs.length) ∧
      (∀ i, c i = 0 ↔ i ∈ Set.range (tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le)) ∧
      (∀ j (hj : j < bs.length), (Finset.univ.filter (fun i => c i = j+1)).card = bs[j]) ∧
      (∀ (g : Equiv.Perm (Fin μ.card)) (h : Equiv.Perm (Fin ν.card)),
        (∀ i, c (g i) = c i) →
        (∀ k, g (tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le k) =
          tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le (h k)) →
        ∀ x, F (spechtRep (shapeTableau μ) g x) = spechtRep (shapeTableau ν) h (F x)) := by
  classical
  induction hs with
  | nil ν =>
    refine ⟨fun _ => 0, LinearMap.id, Function.surjective_id, by simp, ?_, ?_, ?_⟩
    · intro i
      constructor
      · intro _; exact ⟨i,tableauInclusion_self _ i⟩
      · intro _; rfl
    · intro j hj; simp at hj
    · intro g h hc he x
      have hh : g = h := by
        apply Equiv.ext
        intro k
        simpa only [tableauInclusion_self] using he k
      subst h
      rfl
  | @snoc bs ν η μ b hs hh hcard ih =>
    obtain ⟨c,F,hF,hc,hzero,hcount,he⟩ := ih
    obtain ⟨P,hP,hPe⟩ := pieri_strip_surjective_uts (shapeTableau η) (shapeTableau μ) hh
    let i := tableauInclusion (shapeTableau η) (shapeTableau μ) hh.1
    let c' := extendColor i c (bs.length+1)
    refine ⟨c', F.comp P, hF.comp hP, ?_, ?_, ?_, ?_⟩
    · intro k
      simpa only [List.length_append, List.length_singleton] using extendColor_le i c bs.length hc k
    · intro k
      constructor
      · intro hk
        change extendColor i c (bs.length+1) k = 0 at hk
        have hr : k ∈ Set.range i := (extendColor_mem i c bs.length hc k).mp (by omega)
        obtain ⟨l,rfl⟩ := hr
        have hl : c l = 0 := (extendColor_apply i c _ l).symm.trans hk
        obtain ⟨j,hj⟩ := (hzero l).mp hl
        refine ⟨j, ?_⟩
        rw [← tableauInclusion_trans (shapeTableau ν) (shapeTableau η) (shapeTableau μ) hs.le hh.1]
        exact congrArg i hj
      · rintro ⟨j,rfl⟩
        rw [← tableauInclusion_trans (shapeTableau ν) (shapeTableau η) (shapeTableau μ) hs.le hh.1]
        change extendColor i c _ (i _) = 0
        rw [extendColor_apply]
        exact (hzero _).mpr ⟨j,rfl⟩
    · intro j hj
      have hjle : j ≤ bs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      rcases lt_or_eq_of_le hjle with hjlt | rfl
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = j+1)).card = _
        rw [extendColor_count_old i c (bs.length+1) (j+1) (by omega), hcount j hjlt,
          List.getElem_append_left hjlt]
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = bs.length+1)).card = _
        rw [extendColor_count_new i c bs.length hc]
        simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        omega
    · intro g h hg hgi x
      have hgmem : ∀ k, g k ∈ Set.range i ↔ k ∈ Set.range i := by
        intro k
        rw [← extendColor_mem i c bs.length hc, ← extendColor_mem i c bs.length hc]
        exact (congrArg (fun c => c ≤ bs.length) (hg k)).to_iff
      let k := restrictPerm i g hgmem
      have hik (l) : i (k l) = g (i l) := restrictPerm_apply i g hgmem l
      have hkcolor (l) : c (k l) = c l := by
        rw [← extendColor_apply i c (bs.length+1) (k l), hik, ← extendColor_apply i c (bs.length+1) l]
        exact hg (i l)
      have hkbase (l) : k (tableauInclusion (shapeTableau ν) (shapeTableau η) hs.le l) =
          tableauInclusion (shapeTableau ν) (shapeTableau η) hs.le (h l) := by
        apply i.injective
        rw [hik]
        change g (tableauInclusion (shapeTableau η) (shapeTableau μ) hh.1 _) =
          tableauInclusion (shapeTableau η) (shapeTableau μ) hh.1 _
        rw [tableauInclusion_trans, tableauInclusion_trans]
        exact hgi l
      change F (P (spechtRep (shapeTableau μ) g x)) = _
      rw [hPe g k (fun l => (hik l).symm), he k h hkcolor hkbase]
      rfl



end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_HorizontalRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma stripRow_bounds (μ : YoungDiagram) (t i : ℕ) :
    μ.rowLen (i+1) ≤ stripRow μ t i ∧ stripRow μ t i ≤ μ.rowLen i := by
  have h := μ.rowLen_anti i (i+1) (by omega)
  dsimp [stripRow]
  omega

@[simp] lemma mem_stripRemove {μ : YoungDiagram} {t i j : ℕ} :
    (i,j) ∈ stripRemove μ t ↔ j < stripRow μ t i := by
  change (i,j) ∈ μ.cells.filter _ ↔ _
  simp only [Finset.mem_filter, YoungDiagram.mem_cells]
  exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_rowLen.mpr
    (lt_of_lt_of_le h (stripRow_bounds μ t i).2), h⟩⟩

@[simp] lemma stripRemove_rowLen (μ : YoungDiagram) (t i : ℕ) :
    (stripRemove μ t).rowLen i = stripRow μ t i := by
  have hh : ∀ j, j < (stripRemove μ t).rowLen i ↔ j < stripRow μ t i := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_stripRemove]
  have h₁ := hh ((stripRemove μ t).rowLen i)
  have h₂ := hh (stripRow μ t i)
  omega

lemma stripRemove_le (μ : YoungDiagram) (t : ℕ) : stripRemove μ t ≤ μ := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

lemma stripRemove_horizontal (μ : YoungDiagram) (t : ℕ) : HorizontalStrip (stripRemove μ t) μ := by
  refine ⟨stripRemove_le μ t, ?_⟩
  intro x hx hxn y hy hyn hcol
  have hhx := YoungDiagram.mem_iff_lt_rowLen.mp hx
  have hhy := YoungDiagram.mem_iff_lt_rowLen.mp hy
  have hnx : stripRow μ t x.1 ≤ x.2 := le_of_not_gt (fun h => hxn (mem_stripRemove.mpr h))
  have hny : stripRow μ t y.1 ≤ y.2 := le_of_not_gt (fun h => hyn (mem_stripRemove.mpr h))
  have hr : x.1 = y.1 := by
    rcases lt_trichotomy x.1 y.1 with hr | hr | hr
    · have hh := μ.rowLen_anti (x.1+1) y.1 (by omega)
      have hb := (stripRow_bounds μ t x.1).1
      omega
    · exact hr
    · have hh := μ.rowLen_anti (y.1+1) x.1 (by omega)
      have hb := (stripRow_bounds μ t y.1).1
      omega
  exact Prod.ext hr hcol

lemma stripRemove_prefix (μ : YoungDiagram) (t k : ℕ) :
    rowPrefix (stripRemove μ t) k + min t (μ.rowLen 0) =
      rowPrefix μ k + min t (μ.rowLen k) := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    have hr : (stripRemove μ t).rowLen k + min t (μ.rowLen k) =
        μ.rowLen k + min t (μ.rowLen (k+1)) := by
      rw [stripRemove_rowLen]
      dsimp [stripRow]
      omega
    simp only [rowPrefix, Finset.sum_range_succ] at ih ⊢
    omega

lemma stripRemove_card (μ : YoungDiagram) (t : ℕ) :
    (stripRemove μ t).card + min t (μ.rowLen 0) = μ.card := by
  have hh := stripRemove_prefix μ t (μ.colLen 0)
  rw [rowPrefix_eq_card μ le_rfl, rowLen_zero_of_height_le μ le_rfl, min_zero, add_zero] at hh
  have ht : (stripRemove μ t).colLen 0 ≤ μ.colLen 0 := by
    by_contra h
    have hm : (μ.colLen 0, 0) ∈ stripRemove μ t := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hh := YoungDiagram.mem_iff_lt_colLen.mp (stripRemove_le μ t hm)
    omega
  rwa [rowPrefix_eq_card _ ht] at hh


lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  simp [rowPrefix, Finset.sum_range_succ]

lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

lemma dominates_stripRemove_last (θ τ : YoungDiagram) (k : ℕ)
    (hh : θ.colLen 0 ≤ k+1) (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    (stripRemove τ (θ.rowLen k)).card = (rowTruncate θ k).card ∧
      Dominates (stripRemove τ (θ.rowLen k)) (rowTruncate θ k) := by
  have hw : θ.rowLen k ≤ τ.rowLen 0 := by
    have hh := hd 1
    simp only [rowPrefix, Finset.sum_range_one] at hh
    exact (θ.rowLen_anti 0 k (Nat.zero_le _)).trans hh
  have hθ : (rowTruncate θ k).card + θ.rowLen k = θ.card := by
    rw [rowTruncate_card, ← rowPrefix_succ, rowPrefix_eq_card θ hh]
  have hτ : (stripRemove τ (θ.rowLen k)).card + θ.rowLen k = τ.card := by
    simpa only [min_eq_left hw] using stripRemove_card τ (θ.rowLen k)
  have hcard : (stripRemove τ (θ.rowLen k)).card = (rowTruncate θ k).card := by omega
  refine ⟨hcard, ?_⟩
  have hsmall (q : ℕ) (hq : q ≤ k) : rowPrefix θ q ≤ rowPrefix (stripRemove τ (θ.rowLen k)) q := by
    have he := stripRemove_prefix τ (θ.rowLen k) q
    rw [min_eq_left hw] at he
    by_cases hr : θ.rowLen k ≤ τ.rowLen q
    · rw [min_eq_left hr] at he
      have hh := hd q
      omega
    · rw [min_eq_right (by omega : τ.rowLen q ≤ θ.rowLen k)] at he
      have hsq := hd (q+1)
      rw [rowPrefix_succ, rowPrefix_succ] at hsq
      have ht := θ.rowLen_anti q k hq
      omega
  intro q
  by_cases hq : q ≤ k
  · rw [rowTruncate_prefix _ _ _ hq]
    exact hsmall q hq
  · have hle := rowPrefix_le_card (rowTruncate θ k) q
    rw [rowTruncate_card] at hle
    exact hle.trans ((hsmall k le_rfl).trans (rowPrefix_mono _ (by omega)))

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_YoungRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/

lemma rowWeights_congr (θ τ : YoungDiagram) (k : ℕ)
    (he : ∀ i < k, θ.rowLen i = τ.rowLen i) : rowWeights θ k = rowWeights τ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rowWeights, rowWeights, ih (fun i hi => he i (by omega)), he k (by omega)]

lemma card_zero_iff_bot (μ : YoungDiagram) : μ.card = 0 ↔ μ = ⊥ := by
  change μ.cells.card = 0 ↔ _
  rw [Finset.card_eq_zero]
  constructor
  · intro h; exact YoungDiagram.ext h
  · intro h; subst μ; rfl

/- The actual constructive sufficiency step in Young's rule. No tableau,
Pieri, or representation hypothesis is assumed by this combinatorial theorem. -/
theorem sizedStripChain_of_dominates (θ τ : YoungDiagram) (k : ℕ)
    (hh : θ.colLen 0 ≤ k) (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    SizedStripChain (rowWeights θ k) ⊥ τ := by
  induction k generalizing θ τ with
  | zero =>
    have hcθ : θ.card = 0 := by
      have he := rowPrefix_eq_card θ hh
      simpa [rowPrefix] using he.symm
    have ht : τ = ⊥ := (card_zero_iff_bot τ).mp (hc.trans hcθ)
    subst τ
    exact SizedStripChain.nil ⊥
  | succ k ih =>
    obtain ⟨hcν,hdν⟩ := dominates_stripRemove_last θ τ k hh hc hd
    have hs := ih (rowTruncate θ k) (stripRemove τ (θ.rowLen k))
      (rowTruncate_height θ k) hcν hdν
    have he : rowWeights (rowTruncate θ k) k = rowWeights θ k := by
      apply rowWeights_congr
      intro i hi
      rw [rowTruncate_rowLen, ite_eq_left hi]
    rw [he] at hs
    apply SizedStripChain.snoc hs (stripRemove_horizontal τ (θ.rowLen k))
    have hw : θ.rowLen k ≤ τ.rowLen 0 := by
      have hp := hd 1
      simp only [rowPrefix, Finset.sum_range_one] at hp
      exact (θ.rowLen_anti 0 k (Nat.zero_le _)).trans hp
    simpa only [min_eq_left hw] using stripRemove_card τ (θ.rowLen k)



lemma rowWeights_getElem (θ : YoungDiagram) (k j : ℕ) (hj : j < k) :
    (rowWeights θ k)[j]'(by rw [rowWeights_length]; exact hj) = θ.rowLen j := by
  induction k with
  | zero => omega
  | succ k ih =>
    change (rowWeights θ k ++ [θ.rowLen k])[j]'(by simpa only [List.length_append, List.length_singleton, rowWeights_length] using hj) = θ.rowLen j
    by_cases h : j < k
    · rw [List.getElem_append_left (by rwa [rowWeights_length]), ih h]
    · have he : j = k := by omega
      subst j
      rw [List.getElem_append_right (by rw [rowWeights_length])]
      simp only [rowWeights_length, Nat.sub_self, List.getElem_singleton]

theorem young_invariant_functional_uts_oai (θ τ : YoungDiagram)
    (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    ∃ (a : Fin τ.card → Fin (θ.colLen 0)) (l : Module.Dual ℂ (Specht (shapeTableau τ))),
      l ≠ 0 ∧
      (∀ j, (Finset.univ.filter (fun i => a i = j)).card = θ.rowLen j) ∧
      (∀ g : Equiv.Perm (Fin τ.card), a ∘ g = a →
        ∀ x, l (spechtRep (shapeTableau τ) g x) = l x) := by
  classical
  let bs := rowWeights θ (θ.colLen 0)
  have hs := sizedStripChain_of_dominates θ τ (θ.colLen 0) le_rfl hc hd
  obtain ⟨c,F,hF,hcB,hzero,hcount,he⟩ := stripChain_restriction hs
  have hpos (i) : 0 < c i := by
    have hz := hzero i
    have hn : ¬ i ∈ Set.range (tableauInclusion (shapeTableau ⊥) (shapeTableau τ) hs.le) := by
      rintro ⟨j,hj⟩
      exact Fin.elim0 j
    have hc0 : c i ≠ 0 := fun h => hn (hz.mp h)
    omega
  have hbound (i) : c i ≤ θ.colLen 0 := by simpa only [rowWeights_length] using hcB i
  let a : Fin τ.card → Fin (θ.colLen 0) := fun i => ⟨c i-1, by have hh := hpos i; have ht := hbound i; omega⟩
  let v : Specht (shapeTableau ⊥) := ⟨polytabloid (shapeTableau ⊥), mem_cyclic _ _⟩
  let l₀ := spechtSelfDual (shapeTableau ⊥) v
  have hl₀ : l₀ ≠ 0 := by
    intro hz
    have hh := (spechtSelfDual (shapeTableau ⊥)).injective (hz.trans (map_zero _).symm)
    exact polytabloid_ne_zero _ (congrArg Subtype.val hh)
  let l := l₀.comp F
  have hl : l ≠ 0 := by
    intro hz
    apply hl₀
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := hF y
    exact LinearMap.congr_fun hz x
  refine ⟨a,l,hl,?_,?_⟩
  · intro j
    have hj : j.val < (rowWeights θ (θ.colLen 0)).length := by rw [rowWeights_length]; exact j.isLt
    rw [← rowWeights_getElem θ (θ.colLen 0) j.val j.isLt, ← hcount j.val hj]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (⟨c i-1, _⟩ : Fin (θ.colLen 0)) = j ↔ c i = j.val+1
    rw [Fin.ext_iff]
    change c i-1 = j.val ↔ c i = j.val+1
    have hh := hpos i
    omega
  · intro g hg x
    have hcol (i) : c (g i) = c i := by
      have hh := congrArg Fin.val (congrFun hg i)
      change c (g i)-1 = c i-1 at hh
      have hp := hpos i
      have hpg := hpos (g i)
      omega
    have hh := he g 1 hcol (fun k => Fin.elim0 k) x
    change l₀ (F (spechtRep (shapeTableau τ) g x)) = l₀ (F x)
    rw [hh, map_one]
    rfl

end Saxl

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.young_invariant_functional_uts_oai := @OAI.Saxl.young_invariant_functional_uts_oai
