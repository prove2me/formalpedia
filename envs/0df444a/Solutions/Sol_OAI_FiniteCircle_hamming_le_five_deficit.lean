-- Prove2me | solution 1 for OAI.FiniteCircle.hamming_le_five_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:41:45.478644+00:00
-- url     : https://prove2.me/submissions/b65bfee9-8e63-46eb-a7d5-6844e4187fcb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean:L171-L222
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.hamming_le_five_deficit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords

-- ---- from OAI.Combinatorics.FiniteCircle.Matching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace Slide
variable {α : Type*} {x y : List α}

end Slide

namespace SlidePath
variable {α : Type*} {x y z : List α} {n m : ℕ}

end SlidePath

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

theorem exists_lcs_matching {α : Type*} (x y : List α) :
    Nonempty (WordMatching x y (lcs x y)) := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  let e := (Fin.castOrderIso hz.symm).toOrderEmbedding
  exact ⟨⟨e.trans f, e.trans g, fun i => (hf (e i)).symm.trans (hg (e i))⟩⟩

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.CircleWords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem fin_orderEmbedding_lower {q n : ℕ} (e : Fin q ↪o Fin n) (i : Fin q) :
    i.val ≤ (e i).val := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have he := e.strictMono (Fin.castSucc_lt_succ (i := i))
      change (e i.castSucc).val < (e i.succ).val at he
      simpa only [Fin.val_succ, Fin.val_castSucc, Nat.succ_eq_add_one] using (Nat.succ_le_of_lt (ih.trans_lt he))

 theorem fin_orderEmbedding_upper {q n : ℕ} (e : Fin q ↪o Fin n) (i : Fin q) :
    (e i).val ≤ i.val+(n-q) := by
  let r : Fin q ↪o Fin n := OrderEmbedding.ofStrictMono (fun j => (e j.rev).rev) (by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (e.strictMono (Fin.rev_lt_rev.mpr hab)))
  have h := fin_orderEmbedding_lower r i.rev
  change i.rev.val ≤ n-((e i.rev.rev).val+1) at h
  simp only [Fin.rev_rev, Fin.val_rev] at h
  have hqn : q ≤ n := by simpa using Fintype.card_le_of_injective e e.injective
  have hi := i.isLt
  have hei := (e i).isLt
  omega

 theorem threshold_neighborhood_card {n : ℕ} (t E : ℕ) :
    (Finset.univ.filter (fun i : Fin n => t ≤ i.val+E ∧ i.val < t+E)).card ≤ 2*E := by
  classical
  have hc : (Finset.univ.filter (fun i : Fin n => t ≤ i.val+E ∧ i.val < t+E)).card ≤
      (Finset.Ico (t-E) (t+E)).card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro i hi
      have hi := (Finset.mem_filter.mp hi).2
      exact Finset.mem_Ico.mpr ⟨by omega, hi.2⟩
    · intro i _ j _ hij
      exact Fin.ext hij
  rw [Nat.card_Ico] at hc
  omega

theorem hamming_le_five_deficit {n : ℕ} (f g : Fin n → Bool) (t u : ℕ)
    (hg : ∀ i j : Fin n, g i ≠ g j →
      (i.val < t ∧ t ≤ j.val) ∨ (j.val < t ∧ t ≤ i.val) ∨
      (i.val < u ∧ u ≤ j.val) ∨ (j.val < u ∧ u ≤ i.val)) :
    (Finset.univ.filter (fun i => f i ≠ g i)).card ≤
      5*deficit (List.ofFn f) (List.ofFn g) := by
  classical
  obtain ⟨A⟩ := exists_lcs_matching (List.ofFn f) (List.ofFn g)
  let q := lcs (List.ofFn f) (List.ofFn g)
  let E := n-q
  let L : Fin q ↪o Fin n := A.left.trans (Fin.castOrderIso (List.length_ofFn)).toOrderEmbedding
  let R : Fin q ↪o Fin n := A.right.trans (Fin.castOrderIso (List.length_ofFn)).toOrderEmbedding
  have hletters (i : Fin q) : f (L i) = g (R i) := by
    change f (Fin.cast (List.length_ofFn) (A.left i)) = g (Fin.cast (List.length_ofFn) (A.right i))
    simpa only [List.get_ofFn] using A.letters i
  have hdisp (i : Fin q) : (L i).val ≤ (R i).val+E ∧ (R i).val ≤ (L i).val+E := by
    have hl := fin_orderEmbedding_lower L i
    have hu := fin_orderEmbedding_upper L i
    have hl' := fin_orderEmbedding_lower R i
    have hu' := fin_orderEmbedding_upper R i
    exact ⟨by omega, by omega⟩
  let U := Finset.univ \ (Finset.univ.image L)
  let B (a : ℕ) := Finset.univ.filter (fun i : Fin n => a ≤ i.val+E ∧ i.val < a+E)
  have hUC : U.card = E := by
    dsimp [U, E]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_image_of_injective _ L.injective]
    simp
  have hsub : Finset.univ.filter (fun i => f i ≠ g i) ⊆ U ∪ (B t ∪ B u) := by
    intro i hi
    have hd := (Finset.mem_filter.mp hi).2
    by_cases hu : i ∈ U
    · exact Finset.mem_union_left _ hu
    · have him : i ∈ Finset.univ.image L := by simpa [U] using hu
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp him
      have hg' : g (L k) ≠ g (R k) := by rw [← hletters]; exact Ne.symm hd
      have hc := hg (L k) (R k) hg'
      have hm := hdisp k
      apply Finset.mem_union_right
      rcases hc with hc | hc | hc | hc
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le U (B t ∪ B u))
  have hb := Finset.card_union_le (B t) (B u)
  have ht := threshold_neighborhood_card (n := n) t E
  have hu := threshold_neighborhood_card (n := n) u E
  change (B t).card ≤ 2*E at ht
  change (B u).card ≤ 2*E at hu
  have hde : deficit (List.ofFn f) (List.ofFn g) = E := by simp [deficit, E, q]
  rw [hde]
  omega

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.hamming_le_five_deficit := @_root_.OAI.FiniteCircle.hamming_le_five_deficit
