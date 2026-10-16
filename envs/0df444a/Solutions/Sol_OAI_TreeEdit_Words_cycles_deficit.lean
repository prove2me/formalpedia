-- Prove2me | solution 1 for OAI.TreeEdit.Words.cycles_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:42:42.316989+00:00
-- url     : https://prove2.me/submissions/dee563e9-d119-44d9-bb96-f66a488e877b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CyclicWords.lean:L121-L156
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.Words.cycles_deficit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Theorems.Thm_OAI_TreeEdit_Alignment_le_lcs
import Theorems.Thm_OAI_TreeEdit_cycle_charging

-- ---- from OAI.Combinatorics.TreeEdit.Alignments ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

namespace Alignment

variable {n : ℕ}

end Alignment

theorem exists_lcs_alignment (x y : List α) : Nonempty (Alignment x y (lcs x y)) := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  refine ⟨⟨(Fin.castOrderIso hz.symm).toOrderEmbedding.comp f,
    (Fin.castOrderIso hz.symm).toOrderEmbedding.comp g, ?_⟩⟩
  intro i
  exact (hf (Fin.cast hz.symm i)).symm.trans (hg (Fin.cast hz.symm i))

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CyclicWords ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace Words

variable {β : Type*} {n : ℕ}

lemma cycle_coordinates {m T B : ℕ} (r : Fin (T * (m * B))) :
    r.val = r.divNat.val * (m * B) + r.modNat.divNat.val * B +
      r.modNat.modNat.val := by
  dsimp [Fin.divNat, Fin.modNat]
  have h1 := Nat.mod_add_div r.val (m * B)
  have h2 := Nat.mod_add_div (r.val % (m * B)) B
  nlinarith

lemma cycle_offset_strict {m T B : ℕ} {r s : Fin (T * (m * B))}
    (ha : r.divNat = s.divNat) (hi : r.modNat.divNat = s.modNat.divNat)
    (hrs : r < s) : r.modNat.modNat < s.modNat.modNat := by
  have hr := cycle_coordinates r
  have hs := cycle_coordinates s
  rw [ha, hi] at hr
  change r.modNat.modNat.val < s.modNat.modNat.val
  change r.val < s.val at hrs
  omega

lemma cycle_block_alignment {m T B N : ℕ} {β : Fin m → Type*}
    (x y : Fin T → ∀ i, Word (β i) B)
    (f g : Fin N ↪o Fin (T * (m * B)))
    (hfg : ∀ j, get (cycles x) (f j) = get (cycles y) (g j))
    (s : Finset (Fin N)) (a b : Fin T) (i : Fin m)
    (hf : ∀ j ∈ s, (f j).divNat = a ∧ (f j).modNat.divNat = i)
    (hg : ∀ j ∈ s, (g j).divNat = b ∧ (g j).modNat.divNat = i) :
    s.card ≤ lcs (x a i).val (y b i).val := by
  let e := s.orderEmbOfFin rfl
  have hf' (j : Fin s.card) := hf (e j) (s.orderEmbOfFin_mem rfl j)
  have hg' (j : Fin s.card) := hg (e j) (s.orderEmbOfFin_mem rfl j)
  let fl : Fin s.card → Fin B := fun j => (f (e j)).modNat.modNat
  let gr : Fin s.card → Fin B := fun j => (g (e j)).modNat.modNat
  have hfl : StrictMono fl := by
    intro j k hjk
    exact cycle_offset_strict ((hf' j).1.trans (hf' k).1.symm)
      ((hf' j).2.trans (hf' k).2.symm) (f.strictMono (e.strictMono hjk))
  have hgr : StrictMono gr := by
    intro j k hjk
    exact cycle_offset_strict ((hg' j).1.trans (hg' k).1.symm)
      ((hg' j).2.trans (hg' k).2.symm) (g.strictMono (e.strictMono hjk))
  apply Alignment.le_lcs ⟨(OrderEmbedding.ofStrictMono fl hfl).comp
      (Fin.castOrderIso (x a i).property.symm).toOrderEmbedding,
    (OrderEmbedding.ofStrictMono gr hgr).comp
      (Fin.castOrderIso (y b i).property.symm).toOrderEmbedding, ?_⟩
  intro j
  have hh := hfg (e j)
  simp only [at_cycles] at hh
  have h1 := hf' j
  have h2 := hg' j
  rcases h1 with ⟨h1a, h1i⟩
  rcases h2 with ⟨h2a, h2i⟩
  rw [h1a, h1i, h2a, h2i] at hh
  exact eq_of_heq (Sigma.mk.inj hh).2

lemma cycle_fiber_bound {m T B N : ℕ} {β : Fin m → Type*}
    (x y : Fin T → ∀ i, Word (β i) B)
    (f g : Fin N ↪o Fin (T * (m * B)))
    (hfg : ∀ j, get (cycles x) (f j) = get (cycles y) (g j))
    (s : Finset (Fin N)) (a b : Fin T)
    (hf : ∀ j ∈ s, (f j).divNat = a)
    (hg : ∀ j ∈ s, (g j).divNat = b) :
    s.card ≤ ∑ i : Fin m, lcs (x a i).val (y b i).val := by
  classical
  have he : s.card = ∑ i : Fin m, (s.filter (fun j => (f j).modNat.divNat = i)).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (s := s) (t := Finset.univ) (f := fun j => (f j).modNat.divNat) (by simp)
  rw [he]
  apply Finset.sum_le_sum
  intro i _
  apply cycle_block_alignment x y f g hfg _ a b i
  · intro j hj
    exact ⟨hf j (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
  · intro j hj
    have heq := congrArg Sigma.fst (hfg j)
    simp only [at_cycles] at heq
    exact ⟨hg j (Finset.mem_filter.mp hj).1, heq.symm.trans (Finset.mem_filter.mp hj).2⟩

lemma cycles_deficit {m T B : ℕ} {β : Fin m → Type*} (hm : 2 ≤ m) (hB : 0 < B)
    (x y : Fin T → ∀ i, Word (β i) B) (δ : ℝ)
    (hδ : δ ≤ ((m - 2) * B : ℕ))
    (hblocks : ∀ a b, δ ≤ ∑ i : Fin m, (deficit (x a i).val (y b i).val : ℝ)) :
    (T : ℝ) * δ ≤ 2 * (deficit (cycles x).val (cycles y).val : ℝ) := by
  classical
  obtain ⟨al⟩ := exists_lcs_alignment (cycles x).val (cycles y).val
  let f := al.left.comp (Fin.castOrderIso (cycles x).property).toOrderEmbedding
  let g := al.right.comp (Fin.castOrderIso (cycles y).property).toOrderEmbedding
  have hfg (j) : get (cycles x) (f j) = get (cycles y) (g j) := al.agree j
  have hC : 0 < m * B := by positivity
  have hc (j) : (f j).val / B % m = (g j).val / B % m := by
    have he := congrArg Sigma.fst (hfg j)
    have hv := congrArg Fin.val he
    simp only [at_cycles, Fin.divNat, Fin.modNat] at hv
    simpa only [Nat.mul_comm m, Nat.mod_mul_right_div_self] using hv
  have hh := cycle_charging hm hB f g hc δ hδ (by
    intro a b hb
    let s := Finset.univ.filter (fun j => blockIndex hC (f j) = a)
    have hf' (j) (hj : j ∈ s) : (f j).divNat = a := (Finset.mem_filter.mp hj).2
    have hg' (j) (hj : j ∈ s) : (g j).divNat = b := hb j hj
    have hn := cycle_fiber_bound x y f g hfg s a b hf' hg'
    have hle (i : Fin m) : lcs (x a i).val (y b i).val ≤ B := by
      simpa [(x a i).property] using lcs_le_length_left (x a i).val (y b i).val
    have hs : (∑ i : Fin m, deficit (x a i).val (y b i).val) =
        m * B - ∑ i : Fin m, lcs (x a i).val (y b i).val := by
      simp only [deficit, (x a _).property]
      rw [Finset.sum_tsub_distrib _ (fun i _ => hle i)]
      simp
    have hsum : (∑ i : Fin m, (deficit (x a i).val (y b i).val : ℝ)) =
        ((m * B - ∑ i : Fin m, lcs (x a i).val (y b i).val : ℕ) : ℝ) := by
      exact_mod_cast hs
    have hb' := hblocks a b
    rw [hsum] at hb'
    exact hb'.trans (by exact_mod_cast Nat.sub_le_sub_left hn (m * B)))
  simpa only [deficit, (cycles x).property] using hh

end Words

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.Words
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TreeEdit.Words.cycles_deficit := @_root_.OAI.TreeEdit.Words.cycles_deficit
