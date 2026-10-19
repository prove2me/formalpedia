-- Prove2me | solution 1 for OAI.Saxl.young_invariant_functional
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:07:46.511315+00:00
-- url     : https://prove2.me/submissions/e900b7b8-5d52-4840-bacf-780fd158ebdb

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/YoungRule.lean:L120-L176
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.young_invariant_functional. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Theorems.Thm_OAI_Saxl_dominates_stripRemove_last
import Theorems.Thm_OAI_Saxl_polytabloid_rowWord
import Theorems.Thm_OAI_Saxl_stripChain_restriction
import Theorems.Thm_OAI_Saxl_stripRemove_horizontal

-- ---- from OAI.RepresentationTheory.Saxl.SpechtSubmodule ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

/- The actual row-tabloid permutation module, embedded in the word space. -/
/- The Ferrers shape forces the column antisymmetrizer to have rank one
on the row-tabloid module. -/
/- On words, precomposition by a position permutation is a bijection. -/
lemma polytabloid_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t ≠ 0 := by
  intro h
  have hh := congrFun h (rowWord t)
  rw [polytabloid_rowWord] at hh
  exact one_ne_zero hh

/- Every nonzero vector in the genuine complex Specht cyclic subspace
again generates that whole subspace. -/
/- Inclusion of a subrepresentation of a subrepresentation into the ambient space. -/
/- The complex polytabloid module is irreducible. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.HorizontalRemoval ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
lemma rowLen_zero_of_height_le (μ : YoungDiagram) {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  have hm := YoungDiagram.mem_iff_lt_rowLen.mpr h
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

lemma rowPrefix_eq_card (μ : YoungDiagram) {k : ℕ} (hk : μ.colLen 0 ≤ k) :
    rowPrefix μ k = μ.card := by
  have he : μ.card = ∑ i : Fin (μ.colLen 0), μ.rowLen i := by
    have hh := Fintype.card_congr (rowCellEquiv μ)
    simpa using hh
  rw [he, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro i hik hin
  exact rowLen_zero_of_height_le μ (by simpa using hin)

/- Tallest-column bottom deletion, expressed by interlacing rows. -/
lemma stripRemove_le (μ : YoungDiagram) (t : ℕ) : stripRemove μ t ≤ μ := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

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

lemma rowTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (rowTruncate μ k).rowLen i = if i < k then μ.rowLen i else 0 := by
  have hh : ∀ j, j < (rowTruncate μ k).rowLen i ↔ j < if i < k then μ.rowLen i else 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rowTruncate, YoungDiagram.mem_iff_lt_rowLen]
    split_ifs <;> simp_all
  have h₁ := hh ((rowTruncate μ k).rowLen i)
  have h₂ := hh (if i < k then μ.rowLen i else 0)
  omega

lemma rowTruncate_height (μ : YoungDiagram) (k : ℕ) : (rowTruncate μ k).colLen 0 ≤ k := by
  by_contra h
  have hm : (k,0) ∈ rowTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  exact Nat.lt_irrefl k (mem_rowTruncate.mp hm).2

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.YoungRule ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

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

/- Young's sufficiency in the exact form needed for the repeated-row quotient:
a dominant Specht has a nonzero invariant functional for a word of the
prescribed content. -/
theorem young_invariant_functional (θ τ : YoungDiagram)
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

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.young_invariant_functional := @_root_.OAI.Saxl.young_invariant_functional
