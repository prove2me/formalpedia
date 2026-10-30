-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_equations_range_144_304
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:54:35.231687+00:00
-- url     : https://prove2.me/submissions/4c431a13-523c-4ac8-b5d6-02b115c8a687

import Mathlib
import Definitions.Def_SnakyCertificate
import Definitions.Def_OAIQ114S000

section
-- module Solutions.OAIQ114_SC.Compat
attribute [-instance] _root_.OAI.SnakyCertificate.digitModulus_neZero _root_.OAI.SnakyCertificate.rotationModulus_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Lists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem mem_mergeFuel (z : Cell) (n : ℕ) (xs ys : List Cell) :
    z ∈ mergeFuel n xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  induction n generalizing xs ys with
  | zero => simp [mergeFuel]
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [mergeFuel]
        split
        · rename_i h; subst y
          simp only [List.mem_cons, ih]
          tauto
        · split <;> simp only [List.mem_cons, ih] <;> tauto

@[simp] theorem mem_mergeUnion (z : Cell) (xs ys : List Cell) :
    z ∈ mergeUnion xs ys ↔ z ∈ xs ∨ z ∈ ys :=
  mem_mergeFuel z _ xs ys

@[simp] theorem toFinset_mergeUnion (xs ys : List Cell) :
    (mergeUnion xs ys).toFinset = xs.toFinset ∪ ys.toFinset := by
  ext z; simp

theorem mem_sortFuel (z : Cell) (n : ℕ) (xs : List Cell) :
    z ∈ sortFuel n xs ↔ z ∈ xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    simp only [sortFuel]
    split
    · rfl
    · rw [mem_mergeUnion, ih, ih, ← List.mem_append, List.take_append_drop]

@[simp] theorem toFinset_sorted (xs : List Cell) : (sorted xs).toFinset = xs.toFinset := by
  ext z; simp [sorted, mem_sortFuel]

@[simp] theorem denote_place (t : Term) (d : ListRow) :
    denote (place t d) = placeRow t (denote d) := by
  have heq (xs : List Cell) :
      (sorted (xs.map (keyPlace t))).toFinset = xs.toFinset.image (placement t.rotation t.shift) := by
    ext z
    simp [keyPlace]
  simp only [denote, place, placeRow, heq]

@[simp] theorem toFinset_unions (xs : List (List Cell)) :
    (unions xs).toFinset = (xs.map List.toFinset).foldr (· ∪ ·) ∅ := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [unions]

theorem toFinset_inters (xs : List (List Cell)) (a : List Cell) :
    (xs.foldr (· ∩ ·) a).toFinset = (xs.map List.toFinset).foldr (· ∩ ·) a.toFinset := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all only [List.foldr_cons, List.map_cons, toFinset_inter_cell]

@[simp] theorem toFinset_common (ds : List ListRow) :
    (common (ds.map ListRow.H)).toFinset = commonH (ds.map denote) := by
  cases ds with
  | nil => rfl
  | cons d ds => simp [common, commonH, toFinset_inters, Function.comp_def, denote]

theorem denote_fork (ds : List ListRow) : denote (fork ds) = forkRow (ds.map denote) := by
  have hA : (unions (ds.map ListRow.A)).toFinset = unionA (ds.map denote) := by
    simp [unionA, Function.comp_def, denote]
  have hH : (unions (ds.map ListRow.H)).toFinset = unionH (ds.map denote) := by
    simp [unionH, Function.comp_def, denote]
  have hf (xs : List Cell) :
      (xs.filter (fun p => decide (p ≠ origin))).toFinset = xs.toFinset.erase origin := by
    ext p; simp [and_comm]
  simp only [denote, fork, hf, toFinset_mergeUnion, hA, hH, toFinset_common,
    List.toFinset_cons, List.toFinset_nil]
  simp [forkRow, denote, Function.comp_def]

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_TableList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate

theorem table_toList : table.toList = tableList := by
  simp only [table, Array.toList_append]
  rfl

theorem table_getElem?_eq (k : ℕ) : table[k]? = tableList[k]? := by
  rw [← Array.getElem?_toList, table_toList]

theorem merge_ranges {P : ℕ → Prop} {a b c : ℕ}
    (left : ∀ i, a ≤ i → i < b → P i)
    (right : ∀ i, b ≤ i → i < c → P i) :
    ∀ i, a ≤ i → i < c → P i := by
  intro i hlo hhi
  by_cases h : i < b
  · exact left i hlo h
  · exact right i (by omega) hhi

end SnakyCertificate

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_144 : fork [place ⟨7, 0, 4, 5⟩ cache_7, place ⟨104, 4, 1, 5⟩ cache_104, place ⟨55, 0, 5, 4⟩ cache_55] = cache_144 := by
  decide +kernel

theorem load_entry_144 : entryAt 144 = entry_144 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_144 : CacheEquation 144 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(144 < 6)), load_entry_144]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (denote cache_7), placeRow ⟨104, 4, 1, 5⟩ (denote cache_104), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55)] = denote cache_144
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_144

theorem verified_row_145 : fork [place ⟨0, 5, 4, 5⟩ cache_0, place ⟨91, 0, 3, 4⟩ cache_91] = cache_145 := by
  decide +kernel

theorem load_entry_145 : entryAt 145 = entry_145 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_145 : CacheEquation 145 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(145 < 6)), load_entry_145]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (denote cache_0), placeRow ⟨91, 0, 3, 4⟩ (denote cache_91)] = denote cache_145
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_145

theorem verified_row_146 : fork [place ⟨36, 6, 5, 4⟩ cache_36, place ⟨24, 1, 4, 5⟩ cache_24] = cache_146 := by
  decide +kernel

theorem load_entry_146 : entryAt 146 = entry_146 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_146 : CacheEquation 146 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(146 < 6)), load_entry_146]
  change forkRow [placeRow ⟨36, 6, 5, 4⟩ (denote cache_36), placeRow ⟨24, 1, 4, 5⟩ (denote cache_24)] = denote cache_146
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_146

theorem verified_row_147 : fork [place ⟨53, 0, 1, 5⟩ cache_53, place ⟨44, 2, 5, 4⟩ cache_44] = cache_147 := by
  decide +kernel

theorem load_entry_147 : entryAt 147 = entry_147 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_147 : CacheEquation 147 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(147 < 6)), load_entry_147]
  change forkRow [placeRow ⟨53, 0, 1, 5⟩ (denote cache_53), placeRow ⟨44, 2, 5, 4⟩ (denote cache_44)] = denote cache_147
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_147

theorem verified_row_148 : fork [place ⟨7, 1, 5, 4⟩ cache_7, place ⟨46, 1, 4, 5⟩ cache_46, place ⟨94, 0, 5, 3⟩ cache_94, place ⟨97, 1, 4, 5⟩ cache_97] = cache_148 := by
  decide +kernel

theorem load_entry_148 : entryAt 148 = entry_148 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_148 : CacheEquation 148 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(148 < 6)), load_entry_148]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (denote cache_7), placeRow ⟨46, 1, 4, 5⟩ (denote cache_46), placeRow ⟨94, 0, 5, 3⟩ (denote cache_94), placeRow ⟨97, 1, 4, 5⟩ (denote cache_97)] = denote cache_148
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_148

theorem verified_row_149 : fork [place ⟨16, 1, 4, 3⟩ cache_16, place ⟨24, 2, 5, 4⟩ cache_24] = cache_149 := by
  decide +kernel

theorem load_entry_149 : entryAt 149 = entry_149 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_149 : CacheEquation 149 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(149 < 6)), load_entry_149]
  change forkRow [placeRow ⟨16, 1, 4, 3⟩ (denote cache_16), placeRow ⟨24, 2, 5, 4⟩ (denote cache_24)] = denote cache_149
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_149

theorem verified_row_150 : fork [place ⟨4, 6, 1, 3⟩ cache_4, place ⟨126, 5, 2, 5⟩ cache_126] = cache_150 := by
  decide +kernel

theorem load_entry_150 : entryAt 150 = entry_150 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_150 : CacheEquation 150 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(150 < 6)), load_entry_150]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (denote cache_4), placeRow ⟨126, 5, 2, 5⟩ (denote cache_126)] = denote cache_150
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_150

theorem verified_row_151 : fork [place ⟨2, 1, 4, 3⟩ cache_2, place ⟨101, 2, 6, 3⟩ cache_101] = cache_151 := by
  decide +kernel

theorem load_entry_151 : entryAt 151 = entry_151 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_151 : CacheEquation 151 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(151 < 6)), load_entry_151]
  change forkRow [placeRow ⟨2, 1, 4, 3⟩ (denote cache_2), placeRow ⟨101, 2, 6, 3⟩ (denote cache_101)] = denote cache_151
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_151

theorem verified_row_152 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨73, 1, 7, 4⟩ cache_73] = cache_152 := by
  decide +kernel

theorem load_entry_152 : entryAt 152 = entry_152 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_152 : CacheEquation 152 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(152 < 6)), load_entry_152]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨73, 1, 7, 4⟩ (denote cache_73)] = denote cache_152
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_152

theorem verified_row_153 : fork [place ⟨59, 4, 0, 4⟩ cache_59, place ⟨27, 0, 5, 4⟩ cache_27] = cache_153 := by
  decide +kernel

theorem load_entry_153 : entryAt 153 = entry_153 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_153 : CacheEquation 153 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(153 < 6)), load_entry_153]
  change forkRow [placeRow ⟨59, 4, 0, 4⟩ (denote cache_59), placeRow ⟨27, 0, 5, 4⟩ (denote cache_27)] = denote cache_153
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_153

theorem verified_row_154 : fork [place ⟨7, 6, 4, 3⟩ cache_7, place ⟨104, 0, 7, 5⟩ cache_104] = cache_154 := by
  decide +kernel

theorem load_entry_154 : entryAt 154 = entry_154 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_154 : CacheEquation 154 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(154 < 6)), load_entry_154]
  change forkRow [placeRow ⟨7, 6, 4, 3⟩ (denote cache_7), placeRow ⟨104, 0, 7, 5⟩ (denote cache_104)] = denote cache_154
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_154

theorem verified_row_155 : fork [place ⟨7, 1, 5, 4⟩ cache_7, place ⟨55, 3, 4, 5⟩ cache_55] = cache_155 := by
  decide +kernel

theorem load_entry_155 : entryAt 155 = entry_155 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_155 : CacheEquation 155 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(155 < 6)), load_entry_155]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (denote cache_7), placeRow ⟨55, 3, 4, 5⟩ (denote cache_55)] = denote cache_155
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_155

theorem verified_row_156 : fork [place ⟨11, 0, 2, 4⟩ cache_11, place ⟨98, 2, 2, 4⟩ cache_98, place ⟨33, 0, 2, 3⟩ cache_33] = cache_156 := by
  decide +kernel

theorem load_entry_156 : entryAt 156 = entry_156 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_156 : CacheEquation 156 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(156 < 6)), load_entry_156]
  change forkRow [placeRow ⟨11, 0, 2, 4⟩ (denote cache_11), placeRow ⟨98, 2, 2, 4⟩ (denote cache_98), placeRow ⟨33, 0, 2, 3⟩ (denote cache_33)] = denote cache_156
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_156

theorem verified_row_157 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨57, 1, 5, 6⟩ cache_57] = cache_157 := by
  decide +kernel

theorem load_entry_157 : entryAt 157 = entry_157 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_157 : CacheEquation 157 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(157 < 6)), load_entry_157]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨57, 1, 5, 6⟩ (denote cache_57)] = denote cache_157
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_157

theorem verified_row_158 : fork [place ⟨66, 0, 3, 4⟩ cache_66, place ⟨45, 1, 4, 5⟩ cache_45, place ⟨46, 3, 4, 5⟩ cache_46] = cache_158 := by
  decide +kernel

theorem load_entry_158 : entryAt 158 = entry_158 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_158 : CacheEquation 158 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(158 < 6)), load_entry_158]
  change forkRow [placeRow ⟨66, 0, 3, 4⟩ (denote cache_66), placeRow ⟨45, 1, 4, 5⟩ (denote cache_45), placeRow ⟨46, 3, 4, 5⟩ (denote cache_46)] = denote cache_158
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_158

theorem verified_row_159 : fork [place ⟨45, 3, 4, 5⟩ cache_45, place ⟨65, 1, 4, 5⟩ cache_65, place ⟨7, 3, 3, 4⟩ cache_7] = cache_159 := by
  decide +kernel

theorem load_entry_159 : entryAt 159 = entry_159 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_159 : CacheEquation 159 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(159 < 6)), load_entry_159]
  change forkRow [placeRow ⟨45, 3, 4, 5⟩ (denote cache_45), placeRow ⟨65, 1, 4, 5⟩ (denote cache_65), placeRow ⟨7, 3, 3, 4⟩ (denote cache_7)] = denote cache_159
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_159

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_160 : fork [place ⟨63, 1, 8, 3⟩ cache_63, place ⟨32, 3, 4, 3⟩ cache_32] = cache_160 := by
  decide +kernel

theorem load_entry_160 : entryAt 160 = entry_160 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_160 : CacheEquation 160 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(160 < 6)), load_entry_160]
  change forkRow [placeRow ⟨63, 1, 8, 3⟩ (denote cache_63), placeRow ⟨32, 3, 4, 3⟩ (denote cache_32)] = denote cache_160
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_160

theorem verified_row_161 : fork [place ⟨15, 1, 4, 5⟩ cache_15, place ⟨86, 0, 5, 4⟩ cache_86] = cache_161 := by
  decide +kernel

theorem load_entry_161 : entryAt 161 = entry_161 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_161 : CacheEquation 161 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(161 < 6)), load_entry_161]
  change forkRow [placeRow ⟨15, 1, 4, 5⟩ (denote cache_15), placeRow ⟨86, 0, 5, 4⟩ (denote cache_86)] = denote cache_161
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_161

theorem verified_row_162 : fork [place ⟨7, 3, 3, 4⟩ cache_7, place ⟨127, 1, 4, 5⟩ cache_127, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨157, 0, 3, 3⟩ cache_157] = cache_162 := by
  decide +kernel

theorem load_entry_162 : entryAt 162 = entry_162 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_162 : CacheEquation 162 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(162 < 6)), load_entry_162]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨127, 1, 4, 5⟩ (denote cache_127), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨157, 0, 3, 3⟩ (denote cache_157)] = denote cache_162
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_162

theorem verified_row_163 : fork [place ⟨44, 2, 5, 4⟩ cache_44, place ⟨49, 1, 5, 4⟩ cache_49, place ⟨56, 4, 0, 4⟩ cache_56] = cache_163 := by
  decide +kernel

theorem load_entry_163 : entryAt 163 = entry_163 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_163 : CacheEquation 163 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(163 < 6)), load_entry_163]
  change forkRow [placeRow ⟨44, 2, 5, 4⟩ (denote cache_44), placeRow ⟨49, 1, 5, 4⟩ (denote cache_49), placeRow ⟨56, 4, 0, 4⟩ (denote cache_56)] = denote cache_163
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_163

theorem verified_row_164 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨110, 0, 5, 4⟩ cache_110] = cache_164 := by
  decide +kernel

theorem load_entry_164 : entryAt 164 = entry_164 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_164 : CacheEquation 164 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(164 < 6)), load_entry_164]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨110, 0, 5, 4⟩ (denote cache_110)] = denote cache_164
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_164

theorem verified_row_165 : fork [place ⟨0, 7, 5, 8⟩ cache_0, place ⟨107, 0, 7, 5⟩ cache_107] = cache_165 := by
  decide +kernel

theorem load_entry_165 : entryAt 165 = entry_165 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_165 : CacheEquation 165 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(165 < 6)), load_entry_165]
  change forkRow [placeRow ⟨0, 7, 5, 8⟩ (denote cache_0), placeRow ⟨107, 0, 7, 5⟩ (denote cache_107)] = denote cache_165
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_165

theorem verified_row_166 : fork [place ⟨2, 7, 4, 5⟩ cache_2, place ⟨107, 0, 6, 4⟩ cache_107] = cache_166 := by
  decide +kernel

theorem load_entry_166 : entryAt 166 = entry_166 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_166 : CacheEquation 166 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(166 < 6)), load_entry_166]
  change forkRow [placeRow ⟨2, 7, 4, 5⟩ (denote cache_2), placeRow ⟨107, 0, 6, 4⟩ (denote cache_107)] = denote cache_166
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_166

theorem verified_row_167 : fork [place ⟨57, 0, 5, 4⟩ cache_57, place ⟨57, 4, 0, 4⟩ cache_57] = cache_167 := by
  decide +kernel

theorem load_entry_167 : entryAt 167 = entry_167 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_167 : CacheEquation 167 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(167 < 6)), load_entry_167]
  change forkRow [placeRow ⟨57, 0, 5, 4⟩ (denote cache_57), placeRow ⟨57, 4, 0, 4⟩ (denote cache_57)] = denote cache_167
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_167

theorem verified_row_168 : fork [place ⟨6, 1, 5, 5⟩ cache_6, place ⟨152, 0, 3, 4⟩ cache_152] = cache_168 := by
  decide +kernel

theorem load_entry_168 : entryAt 168 = entry_168 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_168 : CacheEquation 168 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(168 < 6)), load_entry_168]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (denote cache_6), placeRow ⟨152, 0, 3, 4⟩ (denote cache_152)] = denote cache_168
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_168

theorem verified_row_169 : fork [place ⟨28, 3, 4, 5⟩ cache_28, place ⟨63, 1, 8, 3⟩ cache_63] = cache_169 := by
  decide +kernel

theorem load_entry_169 : entryAt 169 = entry_169 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_169 : CacheEquation 169 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(169 < 6)), load_entry_169]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (denote cache_28), placeRow ⟨63, 1, 8, 3⟩ (denote cache_63)] = denote cache_169
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_169

theorem verified_row_170 : fork [place ⟨4, 6, 1, 3⟩ cache_4, place ⟨127, 2, 5, 4⟩ cache_127] = cache_170 := by
  decide +kernel

theorem load_entry_170 : entryAt 170 = entry_170 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_170 : CacheEquation 170 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(170 < 6)), load_entry_170]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (denote cache_4), placeRow ⟨127, 2, 5, 4⟩ (denote cache_127)] = denote cache_170
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_170

theorem verified_row_171 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨91, 0, 0, 5⟩ cache_91] = cache_171 := by
  decide +kernel

theorem load_entry_171 : entryAt 171 = entry_171 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_171 : CacheEquation 171 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(171 < 6)), load_entry_171]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨91, 0, 0, 5⟩ (denote cache_91)] = denote cache_171
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_171

theorem verified_row_172 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨55, 6, 0, 4⟩ cache_55, place ⟨64, 0, 1, 3⟩ cache_64] = cache_172 := by
  decide +kernel

theorem load_entry_172 : entryAt 172 = entry_172 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_172 : CacheEquation 172 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(172 < 6)), load_entry_172]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨55, 6, 0, 4⟩ (denote cache_55), placeRow ⟨64, 0, 1, 3⟩ (denote cache_64)] = denote cache_172
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_172

theorem verified_row_173 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨64, 6, 4, 5⟩ cache_64, place ⟨55, 6, 0, 4⟩ cache_55] = cache_173 := by
  decide +kernel

theorem load_entry_173 : entryAt 173 = entry_173 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_173 : CacheEquation 173 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(173 < 6)), load_entry_173]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨64, 6, 4, 5⟩ (denote cache_64), placeRow ⟨55, 6, 0, 4⟩ (denote cache_55)] = denote cache_173
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_173

theorem verified_row_174 : fork [place ⟨58, 3, 4, 5⟩ cache_58, place ⟨57, 1, 4, 5⟩ cache_57, place ⟨84, 0, 3, 4⟩ cache_84] = cache_174 := by
  decide +kernel

theorem load_entry_174 : entryAt 174 = entry_174 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_174 : CacheEquation 174 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(174 < 6)), load_entry_174]
  change forkRow [placeRow ⟨58, 3, 4, 5⟩ (denote cache_58), placeRow ⟨57, 1, 4, 5⟩ (denote cache_57), placeRow ⟨84, 0, 3, 4⟩ (denote cache_84)] = denote cache_174
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_174

theorem verified_row_175 : fork [place ⟨141, 0, 5, 4⟩ cache_141, place ⟨7, 2, 4, 3⟩ cache_7, place ⟨63, 1, 5, 3⟩ cache_63] = cache_175 := by
  decide +kernel

theorem load_entry_175 : entryAt 175 = entry_175 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_175 : CacheEquation 175 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(175 < 6)), load_entry_175]
  change forkRow [placeRow ⟨141, 0, 5, 4⟩ (denote cache_141), placeRow ⟨7, 2, 4, 3⟩ (denote cache_7), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63)] = denote cache_175
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_175

theorem verified_row_176 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨64, 6, 4, 5⟩ cache_64, place ⟨55, 2, 5, 4⟩ cache_55] = cache_176 := by
  decide +kernel

theorem load_entry_176 : entryAt 176 = entry_176 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_176 : CacheEquation 176 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(176 < 6)), load_entry_176]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨64, 6, 4, 5⟩ (denote cache_64), placeRow ⟨55, 2, 5, 4⟩ (denote cache_55)] = denote cache_176
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_176

theorem verified_row_177 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨136, 3, 5, 4⟩ cache_136] = cache_177 := by
  decide +kernel

theorem load_entry_177 : entryAt 177 = entry_177 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_177 : CacheEquation 177 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(177 < 6)), load_entry_177]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨136, 3, 5, 4⟩ (denote cache_136)] = denote cache_177
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_177

theorem verified_row_178 : fork [place ⟨37, 0, 3, 4⟩ cache_37, place ⟨68, 1, 4, 5⟩ cache_68, place ⟨46, 3, 4, 5⟩ cache_46] = cache_178 := by
  decide +kernel

theorem load_entry_178 : entryAt 178 = entry_178 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_178 : CacheEquation 178 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(178 < 6)), load_entry_178]
  change forkRow [placeRow ⟨37, 0, 3, 4⟩ (denote cache_37), placeRow ⟨68, 1, 4, 5⟩ (denote cache_68), placeRow ⟨46, 3, 4, 5⟩ (denote cache_46)] = denote cache_178
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_178

theorem verified_row_179 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨148, 5, 5, 4⟩ cache_148] = cache_179 := by
  decide +kernel

theorem load_entry_179 : entryAt 179 = entry_179 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_179 : CacheEquation 179 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(179 < 6)), load_entry_179]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨148, 5, 5, 4⟩ (denote cache_148)] = denote cache_179
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_179

theorem verified_row_180 : fork [place ⟨7, 3, 3, 4⟩ cache_7, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨155, 0, 4, 5⟩ cache_155, place ⟨132, 0, 3, 3⟩ cache_132] = cache_180 := by
  decide +kernel

theorem load_entry_180 : entryAt 180 = entry_180 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_180 : CacheEquation 180 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(180 < 6)), load_entry_180]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨155, 0, 4, 5⟩ (denote cache_155), placeRow ⟨132, 0, 3, 3⟩ (denote cache_132)] = denote cache_180
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_180

theorem verified_row_181 : fork [place ⟨24, 3, 4, 5⟩ cache_24, place ⟨87, 2, 6, 4⟩ cache_87, place ⟨90, 0, 7, 5⟩ cache_90] = cache_181 := by
  decide +kernel

theorem load_entry_181 : entryAt 181 = entry_181 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_181 : CacheEquation 181 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(181 < 6)), load_entry_181]
  change forkRow [placeRow ⟨24, 3, 4, 5⟩ (denote cache_24), placeRow ⟨87, 2, 6, 4⟩ (denote cache_87), placeRow ⟨90, 0, 7, 5⟩ (denote cache_90)] = denote cache_181
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_181

theorem verified_row_182 : fork [place ⟨12, 2, 7, 3⟩ cache_12, place ⟨139, 0, 7, 4⟩ cache_139] = cache_182 := by
  decide +kernel

theorem load_entry_182 : entryAt 182 = entry_182 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_182 : CacheEquation 182 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(182 < 6)), load_entry_182]
  change forkRow [placeRow ⟨12, 2, 7, 3⟩ (denote cache_12), placeRow ⟨139, 0, 7, 4⟩ (denote cache_139)] = denote cache_182
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_182

theorem verified_row_183 : fork [place ⟨64, 2, 1, 5⟩ cache_64, place ⟨63, 3, 0, 3⟩ cache_63, place ⟨55, 2, 5, 4⟩ cache_55] = cache_183 := by
  decide +kernel

theorem load_entry_183 : entryAt 183 = entry_183 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_183 : CacheEquation 183 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(183 < 6)), load_entry_183]
  change forkRow [placeRow ⟨64, 2, 1, 5⟩ (denote cache_64), placeRow ⟨63, 3, 0, 3⟩ (denote cache_63), placeRow ⟨55, 2, 5, 4⟩ (denote cache_55)] = denote cache_183
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_183

theorem verified_row_184 : fork [place ⟨34, 3, 4, 2⟩ cache_34, place ⟨35, 2, 5, 4⟩ cache_35] = cache_184 := by
  decide +kernel

theorem load_entry_184 : entryAt 184 = entry_184 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_184 : CacheEquation 184 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(184 < 6)), load_entry_184]
  change forkRow [placeRow ⟨34, 3, 4, 2⟩ (denote cache_34), placeRow ⟨35, 2, 5, 4⟩ (denote cache_35)] = denote cache_184
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_184

theorem verified_row_185 : fork [place ⟨44, 3, 4, 5⟩ cache_44, place ⟨49, 0, 4, 5⟩ cache_49, place ⟨84, 0, 3, 4⟩ cache_84] = cache_185 := by
  decide +kernel

theorem load_entry_185 : entryAt 185 = entry_185 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_185 : CacheEquation 185 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(185 < 6)), load_entry_185]
  change forkRow [placeRow ⟨44, 3, 4, 5⟩ (denote cache_44), placeRow ⟨49, 0, 4, 5⟩ (denote cache_49), placeRow ⟨84, 0, 3, 4⟩ (denote cache_84)] = denote cache_185
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_185

theorem verified_row_186 : fork [place ⟨7, 6, 0, 3⟩ cache_7, place ⟨141, 2, 5, 4⟩ cache_141] = cache_186 := by
  decide +kernel

theorem load_entry_186 : entryAt 186 = entry_186 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_186 : CacheEquation 186 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(186 < 6)), load_entry_186]
  change forkRow [placeRow ⟨7, 6, 0, 3⟩ (denote cache_7), placeRow ⟨141, 2, 5, 4⟩ (denote cache_141)] = denote cache_186
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_186

theorem verified_row_187 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨108, 3, 4, 5⟩ cache_108] = cache_187 := by
  decide +kernel

theorem load_entry_187 : entryAt 187 = entry_187 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_187 : CacheEquation 187 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(187 < 6)), load_entry_187]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨108, 3, 4, 5⟩ (denote cache_108)] = denote cache_187
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_187

theorem verified_row_188 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨112, 5, 7, 4⟩ cache_112] = cache_188 := by
  decide +kernel

theorem load_entry_188 : entryAt 188 = entry_188 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_188 : CacheEquation 188 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(188 < 6)), load_entry_188]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨112, 5, 7, 4⟩ (denote cache_112)] = denote cache_188
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_188

theorem verified_row_189 : fork [place ⟨12, 0, 5, 4⟩ cache_12, place ⟨86, 4, 1, 4⟩ cache_86] = cache_189 := by
  decide +kernel

theorem load_entry_189 : entryAt 189 = entry_189 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_189 : CacheEquation 189 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(189 < 6)), load_entry_189]
  change forkRow [placeRow ⟨12, 0, 5, 4⟩ (denote cache_12), placeRow ⟨86, 4, 1, 4⟩ (denote cache_86)] = denote cache_189
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_189

theorem verified_row_190 : fork [place ⟨46, 0, 5, 4⟩ cache_46, place ⟨85, 2, 3, 3⟩ cache_85, place ⟨111, 3, 4, 3⟩ cache_111] = cache_190 := by
  decide +kernel

theorem load_entry_190 : entryAt 190 = entry_190 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_190 : CacheEquation 190 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(190 < 6)), load_entry_190]
  change forkRow [placeRow ⟨46, 0, 5, 4⟩ (denote cache_46), placeRow ⟨85, 2, 3, 3⟩ (denote cache_85), placeRow ⟨111, 3, 4, 3⟩ (denote cache_111)] = denote cache_190
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_190

theorem verified_row_191 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨145, 0, 4, 5⟩ cache_145] = cache_191 := by
  decide +kernel

theorem load_entry_191 : entryAt 191 = entry_191 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_191 : CacheEquation 191 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(191 < 6)), load_entry_191]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨145, 0, 4, 5⟩ (denote cache_145)] = denote cache_191
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_191

theorem verified_row_192 : fork [place ⟨64, 1, 3, 1⟩ cache_64, place ⟨103, 0, 3, 4⟩ cache_103, place ⟨55, 3, 4, 5⟩ cache_55] = cache_192 := by
  decide +kernel

theorem load_entry_192 : entryAt 192 = entry_192 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_192 : CacheEquation 192 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(192 < 6)), load_entry_192]
  change forkRow [placeRow ⟨64, 1, 3, 1⟩ (denote cache_64), placeRow ⟨103, 0, 3, 4⟩ (denote cache_103), placeRow ⟨55, 3, 4, 5⟩ (denote cache_55)] = denote cache_192
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_192

theorem verified_row_193 : fork [place ⟨6, 6, 2, 3⟩ cache_6, place ⟨162, 1, 7, 4⟩ cache_162] = cache_193 := by
  decide +kernel

theorem load_entry_193 : entryAt 193 = entry_193 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_193 : CacheEquation 193 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(193 < 6)), load_entry_193]
  change forkRow [placeRow ⟨6, 6, 2, 3⟩ (denote cache_6), placeRow ⟨162, 1, 7, 4⟩ (denote cache_162)] = denote cache_193
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_193

theorem verified_row_194 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨146, 4, 2, 5⟩ cache_146] = cache_194 := by
  decide +kernel

theorem load_entry_194 : entryAt 194 = entry_194 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_194 : CacheEquation 194 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(194 < 6)), load_entry_194]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨146, 4, 2, 5⟩ (denote cache_146)] = denote cache_194
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_194

theorem verified_row_195 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨162, 1, 5, 4⟩ cache_162] = cache_195 := by
  decide +kernel

theorem load_entry_195 : entryAt 195 = entry_195 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_195 : CacheEquation 195 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(195 < 6)), load_entry_195]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨162, 1, 5, 4⟩ (denote cache_162)] = denote cache_195
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_195

theorem verified_row_196 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨187, 5, 6, 4⟩ cache_187] = cache_196 := by
  decide +kernel

theorem load_entry_196 : entryAt 196 = entry_196 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_196 : CacheEquation 196 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(196 < 6)), load_entry_196]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨187, 5, 6, 4⟩ (denote cache_187)] = denote cache_196
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_196

theorem verified_row_197 : fork [place ⟨63, 3, 0, 3⟩ cache_63, place ⟨63, 1, 5, 3⟩ cache_63] = cache_197 := by
  decide +kernel

theorem load_entry_197 : entryAt 197 = entry_197 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_197 : CacheEquation 197 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(197 < 6)), load_entry_197]
  change forkRow [placeRow ⟨63, 3, 0, 3⟩ (denote cache_63), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63)] = denote cache_197
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_197

theorem verified_row_198 : fork [place ⟨7, 4, 0, 5⟩ cache_7, place ⟨131, 1, 5, 4⟩ cache_131] = cache_198 := by
  decide +kernel

theorem load_entry_198 : entryAt 198 = entry_198 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_198 : CacheEquation 198 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(198 < 6)), load_entry_198]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (denote cache_7), placeRow ⟨131, 1, 5, 4⟩ (denote cache_131)] = denote cache_198
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_198

theorem verified_row_199 : fork [place ⟨55, 1, 4, 5⟩ cache_55, place ⟨64, 3, 5, 1⟩ cache_64, place ⟨84, 0, 3, 4⟩ cache_84] = cache_199 := by
  decide +kernel

theorem load_entry_199 : entryAt 199 = entry_199 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_199 : CacheEquation 199 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(199 < 6)), load_entry_199]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (denote cache_55), placeRow ⟨64, 3, 5, 1⟩ (denote cache_64), placeRow ⟨84, 0, 3, 4⟩ (denote cache_84)] = denote cache_199
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_199

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_200 : fork [place ⟨103, 0, 3, 4⟩ cache_103, place ⟨64, 3, 5, 1⟩ cache_64, place ⟨55, 1, 4, 5⟩ cache_55] = cache_200 := by
  decide +kernel

theorem load_entry_200 : entryAt 200 = entry_200 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_200 : CacheEquation 200 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(200 < 6)), load_entry_200]
  change forkRow [placeRow ⟨103, 0, 3, 4⟩ (denote cache_103), placeRow ⟨64, 3, 5, 1⟩ (denote cache_64), placeRow ⟨55, 1, 4, 5⟩ (denote cache_55)] = denote cache_200
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_200

theorem verified_row_201 : fork [place ⟨45, 3, 5, 7⟩ cache_45, place ⟨82, 0, 6, 5⟩ cache_82] = cache_201 := by
  decide +kernel

theorem load_entry_201 : entryAt 201 = entry_201 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_201 : CacheEquation 201 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(201 < 6)), load_entry_201]
  change forkRow [placeRow ⟨45, 3, 5, 7⟩ (denote cache_45), placeRow ⟨82, 0, 6, 5⟩ (denote cache_82)] = denote cache_201
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_201

theorem verified_row_202 : fork [place ⟨150, 0, 5, 4⟩ cache_150, place ⟨7, 0, 4, 5⟩ cache_7, place ⟨108, 0, 5, 4⟩ cache_108] = cache_202 := by
  decide +kernel

theorem load_entry_202 : entryAt 202 = entry_202 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_202 : CacheEquation 202 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(202 < 6)), load_entry_202]
  change forkRow [placeRow ⟨150, 0, 5, 4⟩ (denote cache_150), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7), placeRow ⟨108, 0, 5, 4⟩ (denote cache_108)] = denote cache_202
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_202

theorem verified_row_203 : fork [place ⟨18, 6, 1, 3⟩ cache_18, place ⟨107, 0, 5, 4⟩ cache_107, place ⟨163, 0, 5, 4⟩ cache_163] = cache_203 := by
  decide +kernel

theorem load_entry_203 : entryAt 203 = entry_203 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_203 : CacheEquation 203 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(203 < 6)), load_entry_203]
  change forkRow [placeRow ⟨18, 6, 1, 3⟩ (denote cache_18), placeRow ⟨107, 0, 5, 4⟩ (denote cache_107), placeRow ⟨163, 0, 5, 4⟩ (denote cache_163)] = denote cache_203
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_203

theorem verified_row_204 : fork [place ⟨2, 5, 4, 2⟩ cache_2, place ⟨166, 2, 5, 3⟩ cache_166] = cache_204 := by
  decide +kernel

theorem load_entry_204 : entryAt 204 = entry_204 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_204 : CacheEquation 204 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(204 < 6)), load_entry_204]
  change forkRow [placeRow ⟨2, 5, 4, 2⟩ (denote cache_2), placeRow ⟨166, 2, 5, 3⟩ (denote cache_166)] = denote cache_204
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_204

theorem verified_row_205 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨168, 0, 3, 4⟩ cache_168] = cache_205 := by
  decide +kernel

theorem load_entry_205 : entryAt 205 = entry_205 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_205 : CacheEquation 205 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(205 < 6)), load_entry_205]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨168, 0, 3, 4⟩ (denote cache_168)] = denote cache_205
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_205

theorem verified_row_206 : fork [place ⟨28, 3, 4, 5⟩ cache_28, place ⟨135, 2, 8, 4⟩ cache_135] = cache_206 := by
  decide +kernel

theorem load_entry_206 : entryAt 206 = entry_206 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_206 : CacheEquation 206 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(206 < 6)), load_entry_206]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (denote cache_28), placeRow ⟨135, 2, 8, 4⟩ (denote cache_135)] = denote cache_206
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_206

theorem verified_row_207 : fork [place ⟨28, 3, 4, 5⟩ cache_28, place ⟨127, 0, 8, 4⟩ cache_127] = cache_207 := by
  decide +kernel

theorem load_entry_207 : entryAt 207 = entry_207 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_207 : CacheEquation 207 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(207 < 6)), load_entry_207]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (denote cache_28), placeRow ⟨127, 0, 8, 4⟩ (denote cache_127)] = denote cache_207
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_207

theorem verified_row_208 : fork [place ⟨7, 4, 0, 5⟩ cache_7, place ⟨127, 0, 5, 4⟩ cache_127] = cache_208 := by
  decide +kernel

theorem load_entry_208 : entryAt 208 = entry_208 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_208 : CacheEquation 208 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(208 < 6)), load_entry_208]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (denote cache_7), placeRow ⟨127, 0, 5, 4⟩ (denote cache_127)] = denote cache_208
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_208

theorem verified_row_209 : fork [place ⟨25, 0, 5, 4⟩ cache_25, place ⟨81, 5, 5, 7⟩ cache_81] = cache_209 := by
  decide +kernel

theorem load_entry_209 : entryAt 209 = entry_209 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_209 : CacheEquation 209 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(209 < 6)), load_entry_209]
  change forkRow [placeRow ⟨25, 0, 5, 4⟩ (denote cache_25), placeRow ⟨81, 5, 5, 7⟩ (denote cache_81)] = denote cache_209
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_209

theorem verified_row_210 : fork [place ⟨58, 2, 5, 4⟩ cache_58, place ⟨57, 0, 5, 4⟩ cache_57, place ⟨117, 1, 4, 5⟩ cache_117] = cache_210 := by
  decide +kernel

theorem load_entry_210 : entryAt 210 = entry_210 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_210 : CacheEquation 210 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(210 < 6)), load_entry_210]
  change forkRow [placeRow ⟨58, 2, 5, 4⟩ (denote cache_58), placeRow ⟨57, 0, 5, 4⟩ (denote cache_57), placeRow ⟨117, 1, 4, 5⟩ (denote cache_117)] = denote cache_210
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_210

theorem verified_row_211 : fork [place ⟨49, 5, 5, 4⟩ cache_49, place ⟨6, 6, 0, 3⟩ cache_6] = cache_211 := by
  decide +kernel

theorem load_entry_211 : entryAt 211 = entry_211 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_211 : CacheEquation 211 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(211 < 6)), load_entry_211]
  change forkRow [placeRow ⟨49, 5, 5, 4⟩ (denote cache_49), placeRow ⟨6, 6, 0, 3⟩ (denote cache_6)] = denote cache_211
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_211

theorem verified_row_212 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨188, 0, 0, 5⟩ cache_188] = cache_212 := by
  decide +kernel

theorem load_entry_212 : entryAt 212 = entry_212 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_212 : CacheEquation 212 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(212 < 6)), load_entry_212]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨188, 0, 0, 5⟩ (denote cache_188)] = denote cache_212
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_212

theorem verified_row_213 : fork [place ⟨6, 0, 7, 5⟩ cache_6, place ⟨191, 0, 3, 5⟩ cache_191] = cache_213 := by
  decide +kernel

theorem load_entry_213 : entryAt 213 = entry_213 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_213 : CacheEquation 213 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(213 < 6)), load_entry_213]
  change forkRow [placeRow ⟨6, 0, 7, 5⟩ (denote cache_6), placeRow ⟨191, 0, 3, 5⟩ (denote cache_191)] = denote cache_213
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_213

theorem verified_row_214 : fork [place ⟨7, 3, 3, 4⟩ cache_7, place ⟨108, 3, 4, 5⟩ cache_108, place ⟨95, 0, 5, 2⟩ cache_95] = cache_214 := by
  decide +kernel

theorem load_entry_214 : entryAt 214 = entry_214 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_214 : CacheEquation 214 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(214 < 6)), load_entry_214]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨108, 3, 4, 5⟩ (denote cache_108), placeRow ⟨95, 0, 5, 2⟩ (denote cache_95)] = denote cache_214
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_214

theorem verified_row_215 : fork [place ⟨107, 1, 4, 6⟩ cache_107, place ⟨24, 0, 5, 4⟩ cache_24] = cache_215 := by
  decide +kernel

theorem load_entry_215 : entryAt 215 = entry_215 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_215 : CacheEquation 215 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(215 < 6)), load_entry_215]
  change forkRow [placeRow ⟨107, 1, 4, 6⟩ (denote cache_107), placeRow ⟨24, 0, 5, 4⟩ (denote cache_24)] = denote cache_215
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_215

theorem verified_row_216 : fork [place ⟨7, 6, 0, 3⟩ cache_7, place ⟨155, 5, 5, 4⟩ cache_155] = cache_216 := by
  decide +kernel

theorem load_entry_216 : entryAt 216 = entry_216 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_216 : CacheEquation 216 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(216 < 6)), load_entry_216]
  change forkRow [placeRow ⟨7, 6, 0, 3⟩ (denote cache_7), placeRow ⟨155, 5, 5, 4⟩ (denote cache_155)] = denote cache_216
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_216

theorem verified_row_217 : fork [place ⟨111, 1, 1, 3⟩ cache_111, place ⟨55, 4, 0, 4⟩ cache_55, place ⟨64, 0, 1, 3⟩ cache_64] = cache_217 := by
  decide +kernel

theorem load_entry_217 : entryAt 217 = entry_217 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_217 : CacheEquation 217 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(217 < 6)), load_entry_217]
  change forkRow [placeRow ⟨111, 1, 1, 3⟩ (denote cache_111), placeRow ⟨55, 4, 0, 4⟩ (denote cache_55), placeRow ⟨64, 0, 1, 3⟩ (denote cache_64)] = denote cache_217
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_217

theorem verified_row_218 : fork [place ⟨0, 5, 3, 7⟩ cache_0, place ⟨182, 0, 2, 4⟩ cache_182] = cache_218 := by
  decide +kernel

theorem load_entry_218 : entryAt 218 = entry_218 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_218 : CacheEquation 218 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(218 < 6)), load_entry_218]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (denote cache_0), placeRow ⟨182, 0, 2, 4⟩ (denote cache_182)] = denote cache_218
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_218

theorem verified_row_219 : fork [place ⟨0, 5, 3, 7⟩ cache_0, place ⟨179, 2, 6, 4⟩ cache_179] = cache_219 := by
  decide +kernel

theorem load_entry_219 : entryAt 219 = entry_219 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_219 : CacheEquation 219 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(219 < 6)), load_entry_219]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (denote cache_0), placeRow ⟨179, 2, 6, 4⟩ (denote cache_179)] = denote cache_219
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_219

theorem verified_row_220 : fork [place ⟨56, 4, 0, 4⟩ cache_56, place ⟨63, 1, 5, 3⟩ cache_63, place ⟨144, 2, 5, 4⟩ cache_144, place ⟨154, 6, 5, 4⟩ cache_154, place ⟨155, 1, 5, 4⟩ cache_155] = cache_220 := by
  decide +kernel

theorem load_entry_220 : entryAt 220 = entry_220 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_220 : CacheEquation 220 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(220 < 6)), load_entry_220]
  change forkRow [placeRow ⟨56, 4, 0, 4⟩ (denote cache_56), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨144, 2, 5, 4⟩ (denote cache_144), placeRow ⟨154, 6, 5, 4⟩ (denote cache_154), placeRow ⟨155, 1, 5, 4⟩ (denote cache_155)] = denote cache_220
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_220

theorem verified_row_221 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨180, 5, 5, 4⟩ cache_180] = cache_221 := by
  decide +kernel

theorem load_entry_221 : entryAt 221 = entry_221 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_221 : CacheEquation 221 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(221 < 6)), load_entry_221]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨180, 5, 5, 4⟩ (denote cache_180)] = denote cache_221
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_221

theorem verified_row_222 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨158, 5, 5, 4⟩ cache_158] = cache_222 := by
  decide +kernel

theorem load_entry_222 : entryAt 222 = entry_222 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_222 : CacheEquation 222 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(222 < 6)), load_entry_222]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨158, 5, 5, 4⟩ (denote cache_158)] = denote cache_222
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_222

theorem verified_row_223 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨135, 2, 5, 4⟩ cache_135, place ⟨128, 0, 3, 3⟩ cache_128, place ⟨111, 3, 4, 3⟩ cache_111, place ⟨127, 0, 5, 4⟩ cache_127] = cache_223 := by
  decide +kernel

theorem load_entry_223 : entryAt 223 = entry_223 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_223 : CacheEquation 223 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(223 < 6)), load_entry_223]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨135, 2, 5, 4⟩ (denote cache_135), placeRow ⟨128, 0, 3, 3⟩ (denote cache_128), placeRow ⟨111, 3, 4, 3⟩ (denote cache_111), placeRow ⟨127, 0, 5, 4⟩ (denote cache_127)] = denote cache_223
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_223

theorem verified_row_224 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨212, 0, 6, 3⟩ cache_212] = cache_224 := by
  decide +kernel

theorem load_entry_224 : entryAt 224 = entry_224 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_224 : CacheEquation 224 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(224 < 6)), load_entry_224]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨212, 0, 6, 3⟩ (denote cache_212)] = denote cache_224
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_224

theorem verified_row_225 : fork [place ⟨111, 7, 7, 5⟩ cache_111, place ⟨61, 4, 4, 5⟩ cache_61] = cache_225 := by
  decide +kernel

theorem load_entry_225 : entryAt 225 = entry_225 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_225 : CacheEquation 225 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(225 < 6)), load_entry_225]
  change forkRow [placeRow ⟨111, 7, 7, 5⟩ (denote cache_111), placeRow ⟨61, 4, 4, 5⟩ (denote cache_61)] = denote cache_225
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_225

theorem verified_row_226 : fork [place ⟨10, 6, 0, 3⟩ cache_10, place ⟨203, 0, 5, 4⟩ cache_203, place ⟨33, 0, 2, 3⟩ cache_33, place ⟨193, 0, 2, 4⟩ cache_193] = cache_226 := by
  decide +kernel

theorem load_entry_226 : entryAt 226 = entry_226 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_226 : CacheEquation 226 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(226 < 6)), load_entry_226]
  change forkRow [placeRow ⟨10, 6, 0, 3⟩ (denote cache_10), placeRow ⟨203, 0, 5, 4⟩ (denote cache_203), placeRow ⟨33, 0, 2, 3⟩ (denote cache_33), placeRow ⟨193, 0, 2, 4⟩ (denote cache_193)] = denote cache_226
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_226

theorem verified_row_227 : fork [place ⟨6, 1, 5, 5⟩ cache_6, place ⟨212, 0, 7, 3⟩ cache_212] = cache_227 := by
  decide +kernel

theorem load_entry_227 : entryAt 227 = entry_227 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_227 : CacheEquation 227 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(227 < 6)), load_entry_227]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (denote cache_6), placeRow ⟨212, 0, 7, 3⟩ (denote cache_212)] = denote cache_227
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_227

theorem verified_row_228 : fork [place ⟨82, 0, 6, 5⟩ cache_82, place ⟨68, 3, 5, 7⟩ cache_68] = cache_228 := by
  decide +kernel

theorem load_entry_228 : entryAt 228 = entry_228 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_228 : CacheEquation 228 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(228 < 6)), load_entry_228]
  change forkRow [placeRow ⟨82, 0, 6, 5⟩ (denote cache_82), placeRow ⟨68, 3, 5, 7⟩ (denote cache_68)] = denote cache_228
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_228

theorem verified_row_229 : fork [place ⟨171, 0, 7, 3⟩ cache_171, place ⟨45, 1, 4, 5⟩ cache_45, place ⟨46, 3, 4, 5⟩ cache_46] = cache_229 := by
  decide +kernel

theorem load_entry_229 : entryAt 229 = entry_229 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_229 : CacheEquation 229 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(229 < 6)), load_entry_229]
  change forkRow [placeRow ⟨171, 0, 7, 3⟩ (denote cache_171), placeRow ⟨45, 1, 4, 5⟩ (denote cache_45), placeRow ⟨46, 3, 4, 5⟩ (denote cache_46)] = denote cache_229
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_229

theorem verified_row_230 : fork [place ⟨10, 6, 3, 4⟩ cache_10, place ⟨193, 0, 5, 5⟩ cache_193, place ⟨203, 0, 8, 5⟩ cache_203, place ⟨33, 0, 5, 4⟩ cache_33] = cache_230 := by
  decide +kernel

theorem load_entry_230 : entryAt 230 = entry_230 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_230 : CacheEquation 230 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(230 < 6)), load_entry_230]
  change forkRow [placeRow ⟨10, 6, 3, 4⟩ (denote cache_10), placeRow ⟨193, 0, 5, 5⟩ (denote cache_193), placeRow ⟨203, 0, 8, 5⟩ (denote cache_203), placeRow ⟨33, 0, 5, 4⟩ (denote cache_33)] = denote cache_230
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_230

theorem verified_row_231 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨222, 0, 6, 4⟩ cache_222] = cache_231 := by
  decide +kernel

theorem load_entry_231 : entryAt 231 = entry_231 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_231 : CacheEquation 231 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(231 < 6)), load_entry_231]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨222, 0, 6, 4⟩ (denote cache_222)] = denote cache_231
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_231

theorem verified_row_232 : fork [place ⟨24, 2, 5, 4⟩ cache_24, place ⟨107, 1, 4, 6⟩ cache_107] = cache_232 := by
  decide +kernel

theorem load_entry_232 : entryAt 232 = entry_232 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_232 : CacheEquation 232 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(232 < 6)), load_entry_232]
  change forkRow [placeRow ⟨24, 2, 5, 4⟩ (denote cache_24), placeRow ⟨107, 1, 4, 6⟩ (denote cache_107)] = denote cache_232
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_232

theorem verified_row_233 : fork [place ⟨32, 3, 3, 1⟩ cache_32, place ⟨133, 0, 6, 4⟩ cache_133] = cache_233 := by
  decide +kernel

theorem load_entry_233 : entryAt 233 = entry_233 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_233 : CacheEquation 233 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(233 < 6)), load_entry_233]
  change forkRow [placeRow ⟨32, 3, 3, 1⟩ (denote cache_32), placeRow ⟨133, 0, 6, 4⟩ (denote cache_133)] = denote cache_233
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_233

theorem verified_row_234 : fork [place ⟨180, 4, 4, 5⟩ cache_180, place ⟨37, 0, 3, 4⟩ cache_37, place ⟨129, 0, 5, 3⟩ cache_129, place ⟨63, 0, 3, 5⟩ cache_63] = cache_234 := by
  decide +kernel

theorem load_entry_234 : entryAt 234 = entry_234 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_234 : CacheEquation 234 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(234 < 6)), load_entry_234]
  change forkRow [placeRow ⟨180, 4, 4, 5⟩ (denote cache_180), placeRow ⟨37, 0, 3, 4⟩ (denote cache_37), placeRow ⟨129, 0, 5, 3⟩ (denote cache_129), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63)] = denote cache_234
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_234

theorem verified_row_235 : fork [place ⟨7, 3, 3, 4⟩ cache_7, place ⟨110, 0, 6, 4⟩ cache_110, place ⟨70, 0, 3, 5⟩ cache_70] = cache_235 := by
  decide +kernel

theorem load_entry_235 : entryAt 235 = entry_235 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_235 : CacheEquation 235 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(235 < 6)), load_entry_235]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨110, 0, 6, 4⟩ (denote cache_110), placeRow ⟨70, 0, 3, 5⟩ (denote cache_70)] = denote cache_235
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_235

theorem verified_row_236 : fork [place ⟨38, 1, 4, 5⟩ cache_38, place ⟨122, 7, 3, 4⟩ cache_122, place ⟨181, 0, 2, 3⟩ cache_181, place ⟨30, 1, 4, 3⟩ cache_30] = cache_236 := by
  decide +kernel

theorem load_entry_236 : entryAt 236 = entry_236 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_236 : CacheEquation 236 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(236 < 6)), load_entry_236]
  change forkRow [placeRow ⟨38, 1, 4, 5⟩ (denote cache_38), placeRow ⟨122, 7, 3, 4⟩ (denote cache_122), placeRow ⟨181, 0, 2, 3⟩ (denote cache_181), placeRow ⟨30, 1, 4, 3⟩ (denote cache_30)] = denote cache_236
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_236

theorem verified_row_237 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨172, 0, 7, 4⟩ cache_172] = cache_237 := by
  decide +kernel

theorem load_entry_237 : entryAt 237 = entry_237 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_237 : CacheEquation 237 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(237 < 6)), load_entry_237]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨172, 0, 7, 4⟩ (denote cache_172)] = denote cache_237
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_237

theorem verified_row_238 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨178, 5, 7, 4⟩ cache_178] = cache_238 := by
  decide +kernel

theorem load_entry_238 : entryAt 238 = entry_238 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_238 : CacheEquation 238 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(238 < 6)), load_entry_238]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨178, 5, 7, 4⟩ (denote cache_178)] = denote cache_238
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_238

theorem verified_row_239 : fork [place ⟨0, 4, 7, 3⟩ cache_0, place ⟨174, 4, 3, 5⟩ cache_174] = cache_239 := by
  decide +kernel

theorem load_entry_239 : entryAt 239 = entry_239 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_239 : CacheEquation 239 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(239 < 6)), load_entry_239]
  change forkRow [placeRow ⟨0, 4, 7, 3⟩ (denote cache_0), placeRow ⟨174, 4, 3, 5⟩ (denote cache_174)] = denote cache_239
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_239

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_240 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨237, 0, 2, 4⟩ cache_237] = cache_240 := by
  decide +kernel

theorem load_entry_240 : entryAt 240 = entry_240 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_240 : CacheEquation 240 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(240 < 6)), load_entry_240]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨237, 0, 2, 4⟩ (denote cache_237)] = denote cache_240
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_240

theorem verified_row_241 : fork [place ⟨131, 1, 5, 4⟩ cache_131, place ⟨159, 1, 5, 4⟩ cache_159, place ⟨61, 0, 4, 5⟩ cache_61] = cache_241 := by
  decide +kernel

theorem load_entry_241 : entryAt 241 = entry_241 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_241 : CacheEquation 241 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(241 < 6)), load_entry_241]
  change forkRow [placeRow ⟨131, 1, 5, 4⟩ (denote cache_131), placeRow ⟨159, 1, 5, 4⟩ (denote cache_159), placeRow ⟨61, 0, 4, 5⟩ (denote cache_61)] = denote cache_241
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_241

theorem verified_row_242 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨190, 0, 5, 4⟩ cache_190] = cache_242 := by
  decide +kernel

theorem load_entry_242 : entryAt 242 = entry_242 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_242 : CacheEquation 242 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(242 < 6)), load_entry_242]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨190, 0, 5, 4⟩ (denote cache_190)] = denote cache_242
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_242

theorem verified_row_243 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨233, 0, 2, 5⟩ cache_233] = cache_243 := by
  decide +kernel

theorem load_entry_243 : entryAt 243 = entry_243 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_243 : CacheEquation 243 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(243 < 6)), load_entry_243]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨233, 0, 2, 5⟩ (denote cache_233)] = denote cache_243
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_243

theorem verified_row_244 : fork [place ⟨99, 4, 2, 5⟩ cache_99, place ⟨99, 0, 4, 5⟩ cache_99, place ⟨11, 7, 3, 3⟩ cache_11, place ⟨173, 2, 5, 4⟩ cache_173] = cache_244 := by
  decide +kernel

theorem load_entry_244 : entryAt 244 = entry_244 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_244 : CacheEquation 244 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(244 < 6)), load_entry_244]
  change forkRow [placeRow ⟨99, 4, 2, 5⟩ (denote cache_99), placeRow ⟨99, 0, 4, 5⟩ (denote cache_99), placeRow ⟨11, 7, 3, 3⟩ (denote cache_11), placeRow ⟨173, 2, 5, 4⟩ (denote cache_173)] = denote cache_244
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_244

theorem verified_row_245 : fork [place ⟨64, 0, 1, 3⟩ cache_64, place ⟨175, 4, 0, 4⟩ cache_175, place ⟨143, 6, 4, 5⟩ cache_143, place ⟨186, 6, 0, 4⟩ cache_186] = cache_245 := by
  decide +kernel

theorem load_entry_245 : entryAt 245 = entry_245 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_245 : CacheEquation 245 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(245 < 6)), load_entry_245]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (denote cache_64), placeRow ⟨175, 4, 0, 4⟩ (denote cache_175), placeRow ⟨143, 6, 4, 5⟩ (denote cache_143), placeRow ⟨186, 6, 0, 4⟩ (denote cache_186)] = denote cache_245
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_245

theorem verified_row_246 : fork [place ⟨64, 6, 4, 5⟩ cache_64, place ⟨175, 2, 5, 4⟩ cache_175, place ⟨186, 0, 5, 4⟩ cache_186, place ⟨143, 0, 1, 3⟩ cache_143] = cache_246 := by
  decide +kernel

theorem load_entry_246 : entryAt 246 = entry_246 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_246 : CacheEquation 246 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(246 < 6)), load_entry_246]
  change forkRow [placeRow ⟨64, 6, 4, 5⟩ (denote cache_64), placeRow ⟨175, 2, 5, 4⟩ (denote cache_175), placeRow ⟨186, 0, 5, 4⟩ (denote cache_186), placeRow ⟨143, 0, 1, 3⟩ (denote cache_143)] = denote cache_246
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_246

theorem verified_row_247 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨229, 0, 4, 5⟩ cache_229] = cache_247 := by
  decide +kernel

theorem load_entry_247 : entryAt 247 = entry_247 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_247 : CacheEquation 247 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(247 < 6)), load_entry_247]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨229, 0, 4, 5⟩ (denote cache_229)] = denote cache_247
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_247

theorem verified_row_248 : fork [place ⟨186, 0, 7, 4⟩ cache_186, place ⟨143, 0, 3, 3⟩ cache_143, place ⟨175, 2, 7, 4⟩ cache_175, place ⟨64, 6, 6, 5⟩ cache_64] = cache_248 := by
  decide +kernel

theorem load_entry_248 : entryAt 248 = entry_248 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_248 : CacheEquation 248 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(248 < 6)), load_entry_248]
  change forkRow [placeRow ⟨186, 0, 7, 4⟩ (denote cache_186), placeRow ⟨143, 0, 3, 3⟩ (denote cache_143), placeRow ⟨175, 2, 7, 4⟩ (denote cache_175), placeRow ⟨64, 6, 6, 5⟩ (denote cache_64)] = denote cache_248
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_248

theorem verified_row_249 : fork [place ⟨0, 7, 4, 5⟩ cache_0, place ⟨225, 1, 4, 1⟩ cache_225] = cache_249 := by
  decide +kernel

theorem load_entry_249 : entryAt 249 = entry_249 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_249 : CacheEquation 249 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(249 < 6)), load_entry_249]
  change forkRow [placeRow ⟨0, 7, 4, 5⟩ (denote cache_0), placeRow ⟨225, 1, 4, 1⟩ (denote cache_225)] = denote cache_249
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_249

theorem verified_row_250 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨238, 0, 2, 4⟩ cache_238] = cache_250 := by
  decide +kernel

theorem load_entry_250 : entryAt 250 = entry_250 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_250 : CacheEquation 250 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(250 < 6)), load_entry_250]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨238, 0, 2, 4⟩ (denote cache_238)] = denote cache_250
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_250

theorem verified_row_251 : fork [place ⟨6, 2, 5, 4⟩ cache_6, place ⟨239, 4, 3, 6⟩ cache_239] = cache_251 := by
  decide +kernel

theorem load_entry_251 : entryAt 251 = entry_251 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_251 : CacheEquation 251 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(251 < 6)), load_entry_251]
  change forkRow [placeRow ⟨6, 2, 5, 4⟩ (denote cache_6), placeRow ⟨239, 4, 3, 6⟩ (denote cache_239)] = denote cache_251
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_251

theorem verified_row_252 : fork [place ⟨111, 3, 4, 3⟩ cache_111, place ⟨154, 6, 5, 4⟩ cache_154, place ⟨144, 2, 5, 4⟩ cache_144, place ⟨63, 1, 5, 3⟩ cache_63, place ⟨155, 1, 5, 4⟩ cache_155] = cache_252 := by
  decide +kernel

theorem load_entry_252 : entryAt 252 = entry_252 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_252 : CacheEquation 252 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(252 < 6)), load_entry_252]
  change forkRow [placeRow ⟨111, 3, 4, 3⟩ (denote cache_111), placeRow ⟨154, 6, 5, 4⟩ (denote cache_154), placeRow ⟨144, 2, 5, 4⟩ (denote cache_144), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨155, 1, 5, 4⟩ (denote cache_155)] = denote cache_252
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_252

theorem verified_row_253 : fork [place ⟨29, 3, 3, 0⟩ cache_29, place ⟨177, 1, 6, 2⟩ cache_177] = cache_253 := by
  decide +kernel

theorem load_entry_253 : entryAt 253 = entry_253 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_253 : CacheEquation 253 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(253 < 6)), load_entry_253]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (denote cache_29), placeRow ⟨177, 1, 6, 2⟩ (denote cache_177)] = denote cache_253
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_253

theorem verified_row_254 : fork [place ⟨96, 7, 4, 5⟩ cache_96, place ⟨108, 0, 8, 5⟩ cache_108] = cache_254 := by
  decide +kernel

theorem load_entry_254 : entryAt 254 = entry_254 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_254 : CacheEquation 254 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(254 < 6)), load_entry_254]
  change forkRow [placeRow ⟨96, 7, 4, 5⟩ (denote cache_96), placeRow ⟨108, 0, 8, 5⟩ (denote cache_108)] = denote cache_254
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_254

theorem verified_row_255 : fork [place ⟨69, 0, 3, 3⟩ cache_69, place ⟨205, 0, 5, 5⟩ cache_205, place ⟨7, 3, 3, 4⟩ cache_7] = cache_255 := by
  decide +kernel

theorem load_entry_255 : entryAt 255 = entry_255 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_255 : CacheEquation 255 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(255 < 6)), load_entry_255]
  change forkRow [placeRow ⟨69, 0, 3, 3⟩ (denote cache_69), placeRow ⟨205, 0, 5, 5⟩ (denote cache_205), placeRow ⟨7, 3, 3, 4⟩ (denote cache_7)] = denote cache_255
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_255

theorem verified_row_256 : fork [place ⟨0, 5, 4, 5⟩ cache_0, place ⟨231, 0, 3, 4⟩ cache_231] = cache_256 := by
  decide +kernel

theorem load_entry_256 : entryAt 256 = entry_256 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_256 : CacheEquation 256 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(256 < 6)), load_entry_256]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (denote cache_0), placeRow ⟨231, 0, 3, 4⟩ (denote cache_231)] = denote cache_256
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_256

theorem verified_row_257 : fork [place ⟨4, 1, 5, 4⟩ cache_4, place ⟨235, 0, 4, 5⟩ cache_235] = cache_257 := by
  decide +kernel

theorem load_entry_257 : entryAt 257 = entry_257 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_257 : CacheEquation 257 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(257 < 6)), load_entry_257]
  change forkRow [placeRow ⟨4, 1, 5, 4⟩ (denote cache_4), placeRow ⟨235, 0, 4, 5⟩ (denote cache_235)] = denote cache_257
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_257

theorem verified_row_258 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨227, 0, 4, 5⟩ cache_227] = cache_258 := by
  decide +kernel

theorem load_entry_258 : entryAt 258 = entry_258 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_258 : CacheEquation 258 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(258 < 6)), load_entry_258]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨227, 0, 4, 5⟩ (denote cache_227)] = denote cache_258
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_258

theorem verified_row_259 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨231, 1, 7, 2⟩ cache_231] = cache_259 := by
  decide +kernel

theorem load_entry_259 : entryAt 259 = entry_259 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_259 : CacheEquation 259 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(259 < 6)), load_entry_259]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨231, 1, 7, 2⟩ (denote cache_231)] = denote cache_259
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_259

theorem verified_row_260 : fork [place ⟨0, 5, 4, 6⟩ cache_0, place ⟨231, 0, 3, 5⟩ cache_231] = cache_260 := by
  decide +kernel

theorem load_entry_260 : entryAt 260 = entry_260 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_260 : CacheEquation 260 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(260 < 6)), load_entry_260]
  change forkRow [placeRow ⟨0, 5, 4, 6⟩ (denote cache_0), placeRow ⟨231, 0, 3, 5⟩ (denote cache_231)] = denote cache_260
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_260

theorem verified_row_261 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨242, 0, 6, 4⟩ cache_242] = cache_261 := by
  decide +kernel

theorem load_entry_261 : entryAt 261 = entry_261 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_261 : CacheEquation 261 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(261 < 6)), load_entry_261]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨242, 0, 6, 4⟩ (denote cache_242)] = denote cache_261
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_261

theorem verified_row_262 : fork [place ⟨0, 7, 5, 7⟩ cache_0, place ⟨213, 0, 3, 4⟩ cache_213] = cache_262 := by
  decide +kernel

theorem load_entry_262 : entryAt 262 = entry_262 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_262 : CacheEquation 262 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(262 < 6)), load_entry_262]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (denote cache_0), placeRow ⟨213, 0, 3, 4⟩ (denote cache_213)] = denote cache_262
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_262

theorem verified_row_263 : fork [place ⟨144, 6, 0, 4⟩ cache_144, place ⟨143, 0, 1, 3⟩ cache_143, place ⟨175, 0, 5, 4⟩ cache_175, place ⟨55, 6, 0, 4⟩ cache_55] = cache_263 := by
  decide +kernel

theorem load_entry_263 : entryAt 263 = entry_263 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_263 : CacheEquation 263 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(263 < 6)), load_entry_263]
  change forkRow [placeRow ⟨144, 6, 0, 4⟩ (denote cache_144), placeRow ⟨143, 0, 1, 3⟩ (denote cache_143), placeRow ⟨175, 0, 5, 4⟩ (denote cache_175), placeRow ⟨55, 6, 0, 4⟩ (denote cache_55)] = denote cache_263
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_263

theorem verified_row_264 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨250, 1, 7, 4⟩ cache_250] = cache_264 := by
  decide +kernel

theorem load_entry_264 : entryAt 264 = entry_264 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_264 : CacheEquation 264 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(264 < 6)), load_entry_264]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨250, 1, 7, 4⟩ (denote cache_250)] = denote cache_264
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_264

theorem verified_row_265 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨247, 0, 4, 6⟩ cache_247] = cache_265 := by
  decide +kernel

theorem load_entry_265 : entryAt 265 = entry_265 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_265 : CacheEquation 265 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(265 < 6)), load_entry_265]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨247, 0, 4, 6⟩ (denote cache_247)] = denote cache_265
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_265

theorem verified_row_266 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨242, 0, 5, 4⟩ cache_242] = cache_266 := by
  decide +kernel

theorem load_entry_266 : entryAt 266 = entry_266 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_266 : CacheEquation 266 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(266 < 6)), load_entry_266]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨242, 0, 5, 4⟩ (denote cache_242)] = denote cache_266
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_266

theorem verified_row_267 : fork [place ⟨175, 4, 1, 4⟩ cache_175, place ⟨144, 2, 6, 4⟩ cache_144, place ⟨55, 2, 6, 4⟩ cache_55, place ⟨143, 4, 5, 3⟩ cache_143] = cache_267 := by
  decide +kernel

theorem load_entry_267 : entryAt 267 = entry_267 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_267 : CacheEquation 267 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(267 < 6)), load_entry_267]
  change forkRow [placeRow ⟨175, 4, 1, 4⟩ (denote cache_175), placeRow ⟨144, 2, 6, 4⟩ (denote cache_144), placeRow ⟨55, 2, 6, 4⟩ (denote cache_55), placeRow ⟨143, 4, 5, 3⟩ (denote cache_143)] = denote cache_267
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_267

theorem verified_row_268 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨251, 0, 4, 2⟩ cache_251] = cache_268 := by
  decide +kernel

theorem load_entry_268 : entryAt 268 = entry_268 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_268 : CacheEquation 268 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(268 < 6)), load_entry_268]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨251, 0, 4, 2⟩ (denote cache_251)] = denote cache_268
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_268

theorem verified_row_269 : fork [place ⟨28, 3, 3, 6⟩ cache_28, place ⟨202, 0, 7, 5⟩ cache_202] = cache_269 := by
  decide +kernel

theorem load_entry_269 : entryAt 269 = entry_269 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_269 : CacheEquation 269 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(269 < 6)), load_entry_269]
  change forkRow [placeRow ⟨28, 3, 3, 6⟩ (denote cache_28), placeRow ⟨202, 0, 7, 5⟩ (denote cache_202)] = denote cache_269
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_269

theorem verified_row_270 : fork [place ⟨63, 0, 3, 7⟩ cache_63, place ⟨6, 7, 3, 2⟩ cache_6] = cache_270 := by
  decide +kernel

theorem load_entry_270 : entryAt 270 = entry_270 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_270 : CacheEquation 270 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(270 < 6)), load_entry_270]
  change forkRow [placeRow ⟨63, 0, 3, 7⟩ (denote cache_63), placeRow ⟨6, 7, 3, 2⟩ (denote cache_6)] = denote cache_270
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_270

theorem verified_row_271 : fork [place ⟨107, 2, 7, 3⟩ cache_107, place ⟨107, 3, 4, 6⟩ cache_107] = cache_271 := by
  decide +kernel

theorem load_entry_271 : entryAt 271 = entry_271 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_271 : CacheEquation 271 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(271 < 6)), load_entry_271]
  change forkRow [placeRow ⟨107, 2, 7, 3⟩ (denote cache_107), placeRow ⟨107, 3, 4, 6⟩ (denote cache_107)] = denote cache_271
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_271

theorem verified_row_272 : fork [place ⟨1, 1, 3, 1⟩ cache_1, place ⟨249, 0, 4, 5⟩ cache_249] = cache_272 := by
  decide +kernel

theorem load_entry_272 : entryAt 272 = entry_272 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_272 : CacheEquation 272 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(272 < 6)), load_entry_272]
  change forkRow [placeRow ⟨1, 1, 3, 1⟩ (denote cache_1), placeRow ⟨249, 0, 4, 5⟩ (denote cache_249)] = denote cache_272
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_272

theorem verified_row_273 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨223, 0, 5, 4⟩ cache_223] = cache_273 := by
  decide +kernel

theorem load_entry_273 : entryAt 273 = entry_273 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_273 : CacheEquation 273 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(273 < 6)), load_entry_273]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨223, 0, 5, 4⟩ (denote cache_223)] = denote cache_273
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_273

theorem verified_row_274 : fork [place ⟨6, 7, 3, 1⟩ cache_6, place ⟨240, 0, 5, 5⟩ cache_240] = cache_274 := by
  decide +kernel

theorem load_entry_274 : entryAt 274 = entry_274 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_274 : CacheEquation 274 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(274 < 6)), load_entry_274]
  change forkRow [placeRow ⟨6, 7, 3, 1⟩ (denote cache_6), placeRow ⟨240, 0, 5, 5⟩ (denote cache_240)] = denote cache_274
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_274

theorem verified_row_275 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨198, 4, 0, 4⟩ cache_198, place ⟨44, 2, 5, 4⟩ cache_44] = cache_275 := by
  decide +kernel

theorem load_entry_275 : entryAt 275 = entry_275 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_275 : CacheEquation 275 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(275 < 6)), load_entry_275]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨198, 4, 0, 4⟩ (denote cache_198), placeRow ⟨44, 2, 5, 4⟩ (denote cache_44)] = denote cache_275
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_275

theorem verified_row_276 : fork [place ⟨7, 3, 3, 4⟩ cache_7, place ⟨177, 0, 5, 4⟩ cache_177, place ⟨63, 0, 3, 5⟩ cache_63] = cache_276 := by
  decide +kernel

theorem load_entry_276 : entryAt 276 = entry_276 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_276 : CacheEquation 276 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(276 < 6)), load_entry_276]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨177, 0, 5, 4⟩ (denote cache_177), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63)] = denote cache_276
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_276

theorem verified_row_277 : fork [place ⟨14, 3, 4, 5⟩ cache_14, place ⟨204, 2, 3, 0⟩ cache_204, place ⟨33, 1, 3, 2⟩ cache_33] = cache_277 := by
  decide +kernel

theorem load_entry_277 : entryAt 277 = entry_277 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_277 : CacheEquation 277 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(277 < 6)), load_entry_277]
  change forkRow [placeRow ⟨14, 3, 4, 5⟩ (denote cache_14), placeRow ⟨204, 2, 3, 0⟩ (denote cache_204), placeRow ⟨33, 1, 3, 2⟩ (denote cache_33)] = denote cache_277
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_277

theorem verified_row_278 : fork [place ⟨63, 3, 3, 3⟩ cache_63, place ⟨162, 1, 8, 4⟩ cache_162] = cache_278 := by
  decide +kernel

theorem load_entry_278 : entryAt 278 = entry_278 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_278 : CacheEquation 278 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(278 < 6)), load_entry_278]
  change forkRow [placeRow ⟨63, 3, 3, 3⟩ (denote cache_63), placeRow ⟨162, 1, 8, 4⟩ (denote cache_162)] = denote cache_278
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_278

theorem verified_row_279 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨234, 5, 7, 4⟩ cache_234] = cache_279 := by
  decide +kernel

theorem load_entry_279 : entryAt 279 = entry_279 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_279 : CacheEquation 279 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(279 < 6)), load_entry_279]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨234, 5, 7, 4⟩ (denote cache_234)] = denote cache_279
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_279

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Equations07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_280 : fork [place ⟨184, 0, 1, 5⟩ cache_184, place ⟨116, 2, 4, 3⟩ cache_116] = cache_280 := by
  decide +kernel

theorem load_entry_280 : entryAt 280 = entry_280 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_280 : CacheEquation 280 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(280 < 6)), load_entry_280]
  change forkRow [placeRow ⟨184, 0, 1, 5⟩ (denote cache_184), placeRow ⟨116, 2, 4, 3⟩ (denote cache_116)] = denote cache_280
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_280

theorem verified_row_281 : fork [place ⟨36, 4, 5, 4⟩ cache_36, place ⟨163, 2, 5, 4⟩ cache_163, place ⟨189, 0, 4, 5⟩ cache_189] = cache_281 := by
  decide +kernel

theorem load_entry_281 : entryAt 281 = entry_281 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_281 : CacheEquation 281 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(281 < 6)), load_entry_281]
  change forkRow [placeRow ⟨36, 4, 5, 4⟩ (denote cache_36), placeRow ⟨163, 2, 5, 4⟩ (denote cache_163), placeRow ⟨189, 0, 4, 5⟩ (denote cache_189)] = denote cache_281
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_281

theorem verified_row_282 : fork [place ⟨56, 0, 5, 4⟩ cache_56, place ⟨64, 0, 1, 3⟩ cache_64, place ⟨55, 0, 5, 4⟩ cache_55, place ⟨265, 0, 1, 3⟩ cache_265] = cache_282 := by
  decide +kernel

theorem load_entry_282 : entryAt 282 = entry_282 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_282 : CacheEquation 282 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(282 < 6)), load_entry_282]
  change forkRow [placeRow ⟨56, 0, 5, 4⟩ (denote cache_56), placeRow ⟨64, 0, 1, 3⟩ (denote cache_64), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨265, 0, 1, 3⟩ (denote cache_265)] = denote cache_282
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_282

theorem verified_row_283 : fork [place ⟨64, 0, 1, 3⟩ cache_64, place ⟨196, 1, 4, 3⟩ cache_196, place ⟨55, 2, 5, 4⟩ cache_55] = cache_283 := by
  decide +kernel

theorem load_entry_283 : entryAt 283 = entry_283 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_283 : CacheEquation 283 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(283 < 6)), load_entry_283]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (denote cache_64), placeRow ⟨196, 1, 4, 3⟩ (denote cache_196), placeRow ⟨55, 2, 5, 4⟩ (denote cache_55)] = denote cache_283
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_283

theorem verified_row_284 : fork [place ⟨45, 1, 4, 5⟩ cache_45, place ⟨224, 0, 5, 4⟩ cache_224, place ⟨46, 3, 4, 5⟩ cache_46] = cache_284 := by
  decide +kernel

theorem load_entry_284 : entryAt 284 = entry_284 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_284 : CacheEquation 284 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(284 < 6)), load_entry_284]
  change forkRow [placeRow ⟨45, 1, 4, 5⟩ (denote cache_45), placeRow ⟨224, 0, 5, 4⟩ (denote cache_224), placeRow ⟨46, 3, 4, 5⟩ (denote cache_46)] = denote cache_284
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_284

theorem verified_row_285 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨273, 0, 6, 4⟩ cache_273] = cache_285 := by
  decide +kernel

theorem load_entry_285 : entryAt 285 = entry_285 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_285 : CacheEquation 285 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(285 < 6)), load_entry_285]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨273, 0, 6, 4⟩ (denote cache_273)] = denote cache_285
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_285

theorem verified_row_286 : fork [place ⟨6, 7, 3, 0⟩ cache_6, place ⟨261, 0, 3, 4⟩ cache_261] = cache_286 := by
  decide +kernel

theorem load_entry_286 : entryAt 286 = entry_286 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_286 : CacheEquation 286 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(286 < 6)), load_entry_286]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (denote cache_6), placeRow ⟨261, 0, 3, 4⟩ (denote cache_261)] = denote cache_286
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_286

theorem verified_row_287 : fork [place ⟨64, 0, 1, 3⟩ cache_64, place ⟨55, 0, 5, 4⟩ cache_55, place ⟨56, 0, 5, 4⟩ cache_56, place ⟨264, 4, 4, 5⟩ cache_264] = cache_287 := by
  decide +kernel

theorem load_entry_287 : entryAt 287 = entry_287 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_287 : CacheEquation 287 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(287 < 6)), load_entry_287]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (denote cache_64), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨56, 0, 5, 4⟩ (denote cache_56), placeRow ⟨264, 4, 4, 5⟩ (denote cache_264)] = denote cache_287
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_287

theorem verified_row_288 : fork [place ⟨130, 1, 4, 2⟩ cache_130, place ⟨96, 0, 1, 4⟩ cache_96] = cache_288 := by
  decide +kernel

theorem load_entry_288 : entryAt 288 = entry_288 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_288 : CacheEquation 288 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(288 < 6)), load_entry_288]
  change forkRow [placeRow ⟨130, 1, 4, 2⟩ (denote cache_130), placeRow ⟨96, 0, 1, 4⟩ (denote cache_96)] = denote cache_288
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_288

theorem verified_row_289 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨279, 0, 2, 4⟩ cache_279] = cache_289 := by
  decide +kernel

theorem load_entry_289 : entryAt 289 = entry_289 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_289 : CacheEquation 289 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(289 < 6)), load_entry_289]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨279, 0, 2, 4⟩ (denote cache_279)] = denote cache_289
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_289

theorem verified_row_290 : fork [place ⟨67, 2, 5, 2⟩ cache_67, place ⟨231, 4, 5, 5⟩ cache_231] = cache_290 := by
  decide +kernel

theorem load_entry_290 : entryAt 290 = entry_290 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_290 : CacheEquation 290 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(290 < 6)), load_entry_290]
  change forkRow [placeRow ⟨67, 2, 5, 2⟩ (denote cache_67), placeRow ⟨231, 4, 5, 5⟩ (denote cache_231)] = denote cache_290
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_290

theorem verified_row_291 : fork [place ⟨89, 3, 3, 4⟩ cache_89, place ⟨202, 0, 8, 4⟩ cache_202, place ⟨55, 4, 3, 4⟩ cache_55] = cache_291 := by
  decide +kernel

theorem load_entry_291 : entryAt 291 = entry_291 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_291 : CacheEquation 291 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(291 < 6)), load_entry_291]
  change forkRow [placeRow ⟨89, 3, 3, 4⟩ (denote cache_89), placeRow ⟨202, 0, 8, 4⟩ (denote cache_202), placeRow ⟨55, 4, 3, 4⟩ (denote cache_55)] = denote cache_291
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_291

theorem verified_row_292 : fork [place ⟨39, 0, 3, 4⟩ cache_39, place ⟨219, 3, 3, 4⟩ cache_219, place ⟨79, 1, 4, 3⟩ cache_79] = cache_292 := by
  decide +kernel

theorem load_entry_292 : entryAt 292 = entry_292 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_292 : CacheEquation 292 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(292 < 6)), load_entry_292]
  change forkRow [placeRow ⟨39, 0, 3, 4⟩ (denote cache_39), placeRow ⟨219, 3, 3, 4⟩ (denote cache_219), placeRow ⟨79, 1, 4, 3⟩ (denote cache_79)] = denote cache_292
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_292

theorem verified_row_293 : fork [place ⟨2, 7, 4, 3⟩ cache_2, place ⟨280, 0, 5, 4⟩ cache_280] = cache_293 := by
  decide +kernel

theorem load_entry_293 : entryAt 293 = entry_293 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_293 : CacheEquation 293 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(293 < 6)), load_entry_293]
  change forkRow [placeRow ⟨2, 7, 4, 3⟩ (denote cache_2), placeRow ⟨280, 0, 5, 4⟩ (denote cache_280)] = denote cache_293
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_293

theorem verified_row_294 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨196, 3, 1, 3⟩ cache_196] = cache_294 := by
  decide +kernel

theorem load_entry_294 : entryAt 294 = entry_294 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_294 : CacheEquation 294 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(294 < 6)), load_entry_294]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨196, 3, 1, 3⟩ (denote cache_196)] = denote cache_294
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_294

theorem verified_row_295 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨64, 2, 1, 5⟩ cache_64, place ⟨55, 0, 5, 4⟩ cache_55, place ⟨265, 4, 4, 3⟩ cache_265] = cache_295 := by
  decide +kernel

theorem load_entry_295 : entryAt 295 = entry_295 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_295 : CacheEquation 295 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(295 < 6)), load_entry_295]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨64, 2, 1, 5⟩ (denote cache_64), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨265, 4, 4, 3⟩ (denote cache_265)] = denote cache_295
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_295

theorem verified_row_296 : fork [place ⟨107, 1, 4, 5⟩ cache_107, place ⟨209, 3, 3, 4⟩ cache_209, place ⟨65, 1, 4, 5⟩ cache_65] = cache_296 := by
  decide +kernel

theorem load_entry_296 : entryAt 296 = entry_296 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_296 : CacheEquation 296 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(296 < 6)), load_entry_296]
  change forkRow [placeRow ⟨107, 1, 4, 5⟩ (denote cache_107), placeRow ⟨209, 3, 3, 4⟩ (denote cache_209), placeRow ⟨65, 1, 4, 5⟩ (denote cache_65)] = denote cache_296
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_296

theorem verified_row_297 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨289, 1, 7, 4⟩ cache_289] = cache_297 := by
  decide +kernel

theorem load_entry_297 : entryAt 297 = entry_297 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_297 : CacheEquation 297 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(297 < 6)), load_entry_297]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨289, 1, 7, 4⟩ (denote cache_289)] = denote cache_297
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_297

theorem verified_row_298 : fork [place ⟨24, 2, 7, 3⟩ cache_24, place ⟨24, 6, 3, 3⟩ cache_24, place ⟨107, 4, 3, 4⟩ cache_107, place ⟨195, 0, 7, 4⟩ cache_195] = cache_298 := by
  decide +kernel

theorem load_entry_298 : entryAt 298 = entry_298 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_298 : CacheEquation 298 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(298 < 6)), load_entry_298]
  change forkRow [placeRow ⟨24, 2, 7, 3⟩ (denote cache_24), placeRow ⟨24, 6, 3, 3⟩ (denote cache_24), placeRow ⟨107, 4, 3, 4⟩ (denote cache_107), placeRow ⟨195, 0, 7, 4⟩ (denote cache_195)] = denote cache_298
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_298

theorem verified_row_299 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨284, 0, 4, 5⟩ cache_284] = cache_299 := by
  decide +kernel

theorem load_entry_299 : entryAt 299 = entry_299 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_299 : CacheEquation 299 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(299 < 6)), load_entry_299]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨284, 0, 4, 5⟩ (denote cache_284)] = denote cache_299
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_299

theorem verified_row_300 : fork [place ⟨64, 3, 5, 1⟩ cache_64, place ⟨240, 2, 5, 1⟩ cache_240, place ⟨55, 3, 4, 5⟩ cache_55] = cache_300 := by
  decide +kernel

theorem load_entry_300 : entryAt 300 = entry_300 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_300 : CacheEquation 300 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(300 < 6)), load_entry_300]
  change forkRow [placeRow ⟨64, 3, 5, 1⟩ (denote cache_64), placeRow ⟨240, 2, 5, 1⟩ (denote cache_240), placeRow ⟨55, 3, 4, 5⟩ (denote cache_55)] = denote cache_300
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_300

theorem verified_row_301 : fork [place ⟨59, 0, 5, 4⟩ cache_59, place ⟨57, 0, 5, 4⟩ cache_57, place ⟨258, 4, 4, 5⟩ cache_258] = cache_301 := by
  decide +kernel

theorem load_entry_301 : entryAt 301 = entry_301 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_301 : CacheEquation 301 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(301 < 6)), load_entry_301]
  change forkRow [placeRow ⟨59, 0, 5, 4⟩ (denote cache_59), placeRow ⟨57, 0, 5, 4⟩ (denote cache_57), placeRow ⟨258, 4, 4, 5⟩ (denote cache_258)] = denote cache_301
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_301

theorem verified_row_302 : fork [place ⟨125, 0, 5, 3⟩ cache_125, place ⟨162, 4, 3, 6⟩ cache_162] = cache_302 := by
  decide +kernel

theorem load_entry_302 : entryAt 302 = entry_302 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_302 : CacheEquation 302 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(302 < 6)), load_entry_302]
  change forkRow [placeRow ⟨125, 0, 5, 3⟩ (denote cache_125), placeRow ⟨162, 4, 3, 6⟩ (denote cache_162)] = denote cache_302
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_302

theorem verified_row_303 : fork [place ⟨49, 4, 4, 5⟩ cache_49, place ⟨44, 1, 4, 5⟩ cache_44, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨261, 0, 3, 4⟩ cache_261] = cache_303 := by
  decide +kernel

theorem load_entry_303 : entryAt 303 = entry_303 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_303 : CacheEquation 303 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(303 < 6)), load_entry_303]
  change forkRow [placeRow ⟨49, 4, 4, 5⟩ (denote cache_49), placeRow ⟨44, 1, 4, 5⟩ (denote cache_44), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨261, 0, 3, 4⟩ (denote cache_261)] = denote cache_303
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_303

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Reconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem cache_equations_range_144 : ∀ i, 144 ≤ i → i < 160 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_144
  · exact cache_equation_145
  · exact cache_equation_146
  · exact cache_equation_147
  · exact cache_equation_148
  · exact cache_equation_149
  · exact cache_equation_150
  · exact cache_equation_151
  · exact cache_equation_152
  · exact cache_equation_153
  · exact cache_equation_154
  · exact cache_equation_155
  · exact cache_equation_156
  · exact cache_equation_157
  · exact cache_equation_158
  · exact cache_equation_159

theorem cache_equations_range_160 : ∀ i, 160 ≤ i → i < 176 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_160
  · exact cache_equation_161
  · exact cache_equation_162
  · exact cache_equation_163
  · exact cache_equation_164
  · exact cache_equation_165
  · exact cache_equation_166
  · exact cache_equation_167
  · exact cache_equation_168
  · exact cache_equation_169
  · exact cache_equation_170
  · exact cache_equation_171
  · exact cache_equation_172
  · exact cache_equation_173
  · exact cache_equation_174
  · exact cache_equation_175

theorem cache_equations_range_176 : ∀ i, 176 ≤ i → i < 192 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_176
  · exact cache_equation_177
  · exact cache_equation_178
  · exact cache_equation_179
  · exact cache_equation_180
  · exact cache_equation_181
  · exact cache_equation_182
  · exact cache_equation_183
  · exact cache_equation_184
  · exact cache_equation_185
  · exact cache_equation_186
  · exact cache_equation_187
  · exact cache_equation_188
  · exact cache_equation_189
  · exact cache_equation_190
  · exact cache_equation_191

theorem cache_equations_range_192 : ∀ i, 192 ≤ i → i < 208 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_192
  · exact cache_equation_193
  · exact cache_equation_194
  · exact cache_equation_195
  · exact cache_equation_196
  · exact cache_equation_197
  · exact cache_equation_198
  · exact cache_equation_199
  · exact cache_equation_200
  · exact cache_equation_201
  · exact cache_equation_202
  · exact cache_equation_203
  · exact cache_equation_204
  · exact cache_equation_205
  · exact cache_equation_206
  · exact cache_equation_207

theorem cache_equations_range_208 : ∀ i, 208 ≤ i → i < 224 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_208
  · exact cache_equation_209
  · exact cache_equation_210
  · exact cache_equation_211
  · exact cache_equation_212
  · exact cache_equation_213
  · exact cache_equation_214
  · exact cache_equation_215
  · exact cache_equation_216
  · exact cache_equation_217
  · exact cache_equation_218
  · exact cache_equation_219
  · exact cache_equation_220
  · exact cache_equation_221
  · exact cache_equation_222
  · exact cache_equation_223

theorem cache_equations_range_224 : ∀ i, 224 ≤ i → i < 240 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_224
  · exact cache_equation_225
  · exact cache_equation_226
  · exact cache_equation_227
  · exact cache_equation_228
  · exact cache_equation_229
  · exact cache_equation_230
  · exact cache_equation_231
  · exact cache_equation_232
  · exact cache_equation_233
  · exact cache_equation_234
  · exact cache_equation_235
  · exact cache_equation_236
  · exact cache_equation_237
  · exact cache_equation_238
  · exact cache_equation_239

theorem cache_equations_range_240 : ∀ i, 240 ≤ i → i < 256 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_240
  · exact cache_equation_241
  · exact cache_equation_242
  · exact cache_equation_243
  · exact cache_equation_244
  · exact cache_equation_245
  · exact cache_equation_246
  · exact cache_equation_247
  · exact cache_equation_248
  · exact cache_equation_249
  · exact cache_equation_250
  · exact cache_equation_251
  · exact cache_equation_252
  · exact cache_equation_253
  · exact cache_equation_254
  · exact cache_equation_255

theorem cache_equations_range_256 : ∀ i, 256 ≤ i → i < 272 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_256
  · exact cache_equation_257
  · exact cache_equation_258
  · exact cache_equation_259
  · exact cache_equation_260
  · exact cache_equation_261
  · exact cache_equation_262
  · exact cache_equation_263
  · exact cache_equation_264
  · exact cache_equation_265
  · exact cache_equation_266
  · exact cache_equation_267
  · exact cache_equation_268
  · exact cache_equation_269
  · exact cache_equation_270
  · exact cache_equation_271

theorem cache_equations_range_272 : ∀ i, 272 ≤ i → i < 288 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_272
  · exact cache_equation_273
  · exact cache_equation_274
  · exact cache_equation_275
  · exact cache_equation_276
  · exact cache_equation_277
  · exact cache_equation_278
  · exact cache_equation_279
  · exact cache_equation_280
  · exact cache_equation_281
  · exact cache_equation_282
  · exact cache_equation_283
  · exact cache_equation_284
  · exact cache_equation_285
  · exact cache_equation_286
  · exact cache_equation_287

theorem cache_equations_range_288 : ∀ i, 288 ≤ i → i < 304 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_288
  · exact cache_equation_289
  · exact cache_equation_290
  · exact cache_equation_291
  · exact cache_equation_292
  · exact cache_equation_293
  · exact cache_equation_294
  · exact cache_equation_295
  · exact cache_equation_296
  · exact cache_equation_297
  · exact cache_equation_298
  · exact cache_equation_299
  · exact cache_equation_300
  · exact cache_equation_301
  · exact cache_equation_302
  · exact cache_equation_303

theorem cache_equations_range_144_176 : ∀ i, 144 ≤ i → i < 176 → CacheEquation i :=
  merge_ranges cache_equations_range_144 cache_equations_range_160

theorem cache_equations_range_192_224 : ∀ i, 192 ≤ i → i < 224 → CacheEquation i :=
  merge_ranges cache_equations_range_192 cache_equations_range_208

theorem cache_equations_range_176_224 : ∀ i, 176 ≤ i → i < 224 → CacheEquation i :=
  merge_ranges cache_equations_range_176 cache_equations_range_192_224

theorem cache_equations_range_144_224 : ∀ i, 144 ≤ i → i < 224 → CacheEquation i :=
  merge_ranges cache_equations_range_144_176 cache_equations_range_176_224

theorem cache_equations_range_224_256 : ∀ i, 224 ≤ i → i < 256 → CacheEquation i :=
  merge_ranges cache_equations_range_224 cache_equations_range_240

theorem cache_equations_range_272_304 : ∀ i, 272 ≤ i → i < 304 → CacheEquation i :=
  merge_ranges cache_equations_range_272 cache_equations_range_288

theorem cache_equations_range_256_304 : ∀ i, 256 ≤ i → i < 304 → CacheEquation i :=
  merge_ranges cache_equations_range_256 cache_equations_range_272_304

theorem cache_equations_range_224_304 : ∀ i, 224 ≤ i → i < 304 → CacheEquation i :=
  merge_ranges cache_equations_range_224_256 cache_equations_range_256_304

theorem cache_equations_range_144_304_oai : ∀ i, 144 ≤ i → i < 304 → CacheEquation i :=
  merge_ranges cache_equations_range_144_224 cache_equations_range_224_304

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_equations_range_144_304_oai := @OAI.SnakyCertificate.Check.cache_equations_range_144_304_oai
