-- Prove2me | solution 1 for OAI.EditApproximation.local_physical_conditional_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:38:11.69947+00:00
-- url     : https://prove2.me/submissions/8442a84b-5eb2-4b8a-9e5b-b7cb67312a0e

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_localFinalProgram_accuracy

section
-- module Solutions.OAIQ361V3_EA.EditDistance_Metric
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Unrestricted edit scripts, metric inequalities, and common subsequences
-/

namespace EditDistortion

universe u v

variable {Alpha : Type u} {Beta : Type v} {s : Bool}

namespace Step

theorem map (f : Alpha → Beta) {x y : List Alpha} (h : Step s x y) :
    Step s (x.map f) (y.map f) := by
  cases h with
  | insert p q a => simpa using Step.insert (substitutions := s) (p.map f) (q.map f) (f a)
  | delete p q a => simpa using Step.delete (substitutions := s) (p.map f) (q.map f) (f a)
  | substitute hs p q a b =>
    simpa using Step.substitute hs (p.map f) (q.map f) (f a) (f b)

end Step

namespace Script

theorem map (f : Alpha → Beta) {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    Script s n (x.map f) (y.map f) := by
  induction h with
  | nil x => exact .nil _
  | cons e h ih => exact .cons (e.map f) ih

theorem eq_of_zero {x y : List Alpha} (h : Script s 0 x y) : x = y := by
  cases h
  rfl

end Script



theorem cost_eq_zero_iff {x y : List Alpha} : cost s x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hc := cost_spec (s := s) x y
    rw [h] at hc
    exact hc.eq_of_zero
  · rintro rfl
    exact cost_refl _

theorem cost_map_le (f : Alpha → Beta) (x y : List Alpha) :
    cost s (x.map f) (y.map f) ≤ cost s x y :=
  cost_le ((cost_spec x y).map f)

end EditDistortion

namespace EditDistortion

universe u v
variable {Alpha : Type u} {Beta : Type v} {s : Bool}

theorem cost_map_eq_of_leftInverse (f : Alpha → Beta) (g : Beta → Alpha)
    (h : Function.LeftInverse g f) (x y : List Alpha) :
    cost s (x.map f) (y.map f) = cost s x y := by
  apply Nat.le_antisymm (cost_map_le f x y)
  have H := cost_map_le (s := s) g (x.map f) (y.map f)
  simpa only [List.map_map, h.comp_eq_id, List.map_id] using H

end EditDistortion

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseSeed
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.querySliceHeadWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual bounded-shift coarse tree

Section 3's deterministic shift representation uses a complete finite
branching tree with empty/singleton source leaves. Bounded integer shifts
are encoded by `Fin (2k+1)`; code `k` is shift zero. Virtual target positions
are represented by fresh `none` symbols in a finite surrounding frame.
-/

namespace EditApproximation

open Finset EditDistortion

universe u



theorem substring_one {α : Type u} (word : List α) (position : ℕ) :
    substring word position (position + 1) = word[position]?.toList := by
  rw [substring, ← List.take_drop, List.take_one, List.head?_drop]

/-- Leaf editing costs are at most the literal mismatch/virtual-position
value, including positions outside the finite frame. -/
theorem coarse_leaf_edit_le {B : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (frame : List (Option α)) (letter : Option α) (start : ℕ)
    (shift : Fin (2 * k + 1)) :
    edit ((CoarseSourceTree.leaf (B := B) letter).word.map some)
      (substring frame (start + shift.val)
        (start + shift.val + (CoarseSourceTree.leaf (B := B) letter).word.length)) ≤
      coarseShiftCost k frame (.leaf (B := B) letter) start shift := by
  cases letter with
  | none =>
    simp only [CoarseSourceTree.word, Option.toList_none, List.map_nil, List.length_nil,
      add_zero, coarseShiftCost, substring, List.drop_take_self]
    exact (cost_refl []).le
  | some letter =>
    simp only [CoarseSourceTree.word, Option.toList_some, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil, zero_add, coarseShiftCost]
    rw [substring_one]
    cases hentry : frame[start + shift.val]? with
    | none =>
      simp only [Option.toList_none, Option.getD_none, reduceCtorEq, ↓reduceIte]
      exact (edit_le_max_length [some letter] []).trans (by simp)
    | some entry =>
      simp only [Option.toList_some, Option.getD_some]
      split_ifs with hequal
      · subst entry
        exact (cost_refl [some letter]).le
      · exact (edit_le_max_length [some letter] [entry]).trans (by simp)

/-- Moving both endpoints by a shift change costs at most twice the
absolute difference of their bounded integer codes. -/
theorem coarse_child_shift_edit_le {α : Type u} (frame : List α) (source : List α)
    (start shift next : ℕ) :
    edit source (substring frame (start + shift) (start + shift + source.length)) ≤
      edit source (substring frame (start + next) (start + next + source.length)) +
        2 * Nat.dist shift next := by
  have hmove := edit_substring_endpoints_le frame
    (start + next) (start + next + source.length)
    (start + shift) (start + shift + source.length)
  have hstart : Nat.dist (start + next) (start + shift) = Nat.dist shift next := by
    rw [Nat.dist_add_add_left, Nat.dist_comm]
  have hfinish : Nat.dist (start + next + source.length) (start + shift + source.length) =
      Nat.dist shift next := by rw [Nat.dist_add_add_right, hstart]
  rw [hstart, hfinish] at hmove
  have htriangle := cost_triangle (s := true) source
    (substring frame (start + next) (start + next + source.length))
    (substring frame (start + shift) (start + shift + source.length))
  change edit source (substring frame (start + shift) (start + shift + source.length)) ≤
    edit source (substring frame (start + next) (start + next + source.length)) +
      edit (substring frame (start + next) (start + next + source.length))
        (substring frame (start + shift) (start + shift + source.length)) at htriangle
  exact htriangle.trans (by omega)

/-- Actual child editing and endpoint movement give the recurrence's
lower invariant, proved directly on concatenated source strings. -/
theorem coarseChildrenCost_edit_lower {B D : ℕ} {α : Type u}
    (k : ℕ) (frame : List (Option α))
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : List (CoarseSourceTree B α D))
    (hchild : ∀ child ∈ children, ∀ start shift,
      edit (child.word.map some)
        (substring frame (start + shift.val) (start + shift.val + child.word.length)) ≤
          value child start shift) (start : ℕ) (shift : Fin (2 * k + 1)) :
    edit ((children.map CoarseSourceTree.word).flatten.map some)
      (substring frame (start + shift.val)
        (start + shift.val + (children.map CoarseSourceTree.word).flatten.length)) ≤
      coarseChildrenCost k value children start shift := by
  induction children generalizing start with
  | nil =>
    simp only [List.map_nil, List.flatten_nil, List.length_nil, add_zero, substring,
      List.drop_take_self, coarseChildrenCost]
    exact (cost_refl []).le
  | cons child rest ih =>
    have hfirst : edit (child.word.map some)
        (substring frame (start + shift.val) (start + shift.val + child.word.length)) ≤
      univ.inf' univ_nonempty (fun next => value child start next + 2 * Nat.dist shift.val next.val) := by
      apply le_inf'
      intro next hnext
      have hmove := coarse_child_shift_edit_le frame (child.word.map some) start shift.val next.val
      simp only [List.length_map] at hmove
      exact hmove.trans (Nat.add_le_add_right (hchild child (by simp) start next) _)
    have hrest := ih (fun next hnext => hchild next (by simp [hnext]))
      (start + child.word.length)
    have hsplit := substring_split frame (start + shift.val)
      (start + shift.val + child.word.length)
      (start + shift.val + (child.word ++ (rest.map CoarseSourceTree.word).flatten).length)
      (by omega) (by simp only [List.length_append]; omega)
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.length_append,
      coarseChildrenCost]
    simp only [List.length_append] at hsplit
    rw [hsplit]
    have happend := cost_append_le (s := true) (child.word.map some)
      (substring frame (start + shift.val) (start + shift.val + child.word.length))
      ((rest.map CoarseSourceTree.word).flatten.map some)
      (substring frame (start + shift.val + child.word.length)
        (start + shift.val + child.word.length + (rest.map CoarseSourceTree.word).flatten.length))
    have hrest' : edit ((rest.map CoarseSourceTree.word).flatten.map some)
        (substring frame (start + shift.val + child.word.length)
          (start + shift.val + child.word.length + (rest.map CoarseSourceTree.word).flatten.length)) ≤
        coarseChildrenCost k value rest (start + child.word.length) shift := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest
    have hresult := happend.trans (Nat.add_le_add hfirst hrest')
    change edit _ _ ≤ _ at hresult
    simpa only [Nat.add_assoc] using hresult

/-- The literal bounded-shift tree always dominates edit distance to its
corresponding shifted equal-width target interval. -/
theorem coarseShiftCost_edit_lower {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (frame : List (Option α)) (tree : CoarseSourceTree B α D)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    edit (tree.word.map some)
      (substring frame (start + shift.val) (start + shift.val + tree.word.length)) ≤
      coarseShiftCost k frame tree start shift := by
  induction tree generalizing start shift with
  | leaf letter => exact coarse_leaf_edit_le k frame letter start shift
  | branch children ih =>
    simp only [CoarseSourceTree.word, coarseShiftCost]
    have hword : (List.ofFn children).map CoarseSourceTree.word =
        List.ofFn (fun i => (children i).word) := by
      simp only [List.map_ofFn, Function.comp_def]
    rw [← hword]
    apply coarseChildrenCost_edit_lower k frame
      (fun child => coarseShiftCost k frame child) (List.ofFn children)
    intro child hchild start shift
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchild
    exact ih i start shift

/-- The central equal-width target interval excludes all virtual symbols. -/
theorem coarseTargetFrame_center {α : Type u} (k : ℕ) (target : List α) :
    substring (coarseTargetFrame k target) k (k + target.length) = target.map some := by
  have hprefix : (List.replicate k (none : Option α) ++ target.map some).length = k + target.length := by simp
  rw [substring, coarseTargetFrame, ← hprefix, List.take_append_length]
  simpa only [List.length_replicate] using
    (List.drop_append_length (l₁ := List.replicate k (none : Option α)) (l₂ := target.map some))

/-- First deterministic shift-tree distortion inequality, for the actual
unrestricted unit-cost edit distance and actual finite recurrence. -/
theorem coarseTreeValue_edit_lower {B D : ℕ} {α : Type u} [DecidableEq α] [Inhabited α]
    (tree : CoarseSourceTree B α D) (target : List α) (k : ℕ)
    (hlength : tree.word.length = target.length) :
    edit tree.word target ≤ coarseTreeValue tree target k := by
  have h := coarseShiftCost_edit_lower k (coarseTargetFrame k target) tree 0 (coarseRootShift k)
  simp only [coarseRootShift, zero_add, hlength, coarseTargetFrame_center] at h
  have hmap := cost_map_eq_of_leftInverse (s := true) some
    (fun entry : Option α => entry.getD default) (by intro letter; rfl) tree.word target
  change edit (tree.word.map some) (target.map some) = edit tree.word target at hmap
  rw [hmap] at h
  exact h

theorem coarseChildrenCost_le_width {B D : ℕ} {α : Type u} (k : ℕ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : List (CoarseSourceTree B α D))
    (hchild : ∀ child ∈ children, ∀ start shift, value child start shift ≤ child.word.length)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseChildrenCost k value children start shift ≤ (children.map CoarseSourceTree.word).flatten.length := by
  induction children generalizing start with
  | nil => simp [coarseChildrenCost]
  | cons child rest ih =>
    have hmin := inf'_le (fun next => value child start next + 2 * Nat.dist shift.val next.val)
      (mem_univ shift)
    simp only [Nat.dist_self, mul_zero, add_zero] at hmin
    have hfirst := hchild child (by simp) start shift
    have hrest := ih (fun next hnext => hchild next (by simp [hnext]))
      (start + child.word.length)
    simp only [coarseChildrenCost, List.map_cons, List.flatten_cons, List.length_append]
    omega

/-- Constant shifts give the exact node-width bound used by pruning. -/
theorem coarseShiftCost_le_width {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (frame : List (Option α)) (tree : CoarseSourceTree B α D)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseShiftCost k frame tree start shift ≤ tree.word.length := by
  induction tree generalizing start shift with
  | leaf letter =>
    cases letter with
    | none => simp [coarseShiftCost, CoarseSourceTree.word]
    | some letter =>
      simp only [coarseShiftCost, CoarseSourceTree.word, Option.toList_some,
        List.length_cons, List.length_nil]
      split_ifs <;> omega
  | branch children ih =>
    simp only [CoarseSourceTree.word, coarseShiftCost]
    have hword : (List.ofFn children).map CoarseSourceTree.word =
        List.ofFn (fun i => (children i).word) := by
      simp only [List.map_ofFn, Function.comp_def]
    rw [← hword]
    apply coarseChildrenCost_le_width k (fun child => coarseShiftCost k frame child) (List.ofFn children)
    intro child hchild start shift
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchild
    exact ih i start shift

/-- The literal consecutive capacity chunks cover exactly the permitted
before; zero capacity and empty trailing chunks are included. -/
theorem coarse_capacity_chunks {α : Type u} (source : List α) (B capacity : ℕ) :
    (List.ofFn fun i : Fin B => (source.drop (i.val * capacity)).take capacity).flatten =
      source.take (B * capacity) := by
  induction B generalizing source with
  | zero => simp
  | succ B ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, zero_mul, List.drop_zero, Fin.val_succ]
    have hchunks : (List.ofFn fun i : Fin B =>
        (source.drop ((i.val + 1) * capacity)).take capacity) =
        List.ofFn (fun i : Fin B => ((source.drop capacity).drop (i.val * capacity)).take capacity) := by
      congr 1
      funext i
      simp only [List.drop_drop, Nat.add_mul, one_mul, Nat.add_comm]
    rw [hchunks, ih, ← List.take_add]
    simp only [Nat.succ_mul, Nat.add_comm]

/-- A concrete complete source tree with empty/singleton leaves. Its
recursive child chunks have the capacity prescribed by the remaining depth. -/


theorem coarseSourceTreeOfList_word {α : Type u} (B D : ℕ) (source : List α) :
    (coarseSourceTreeOfList B D source).word = source.take (B ^ D) := by
  induction D generalizing source with
  | zero => simp only [coarseSourceTreeOfList, CoarseSourceTree.word, pow_zero, List.take_one]
  | succ D ih =>
    simp only [coarseSourceTreeOfList, CoarseSourceTree.word, ih, List.take_take, min_self]
    rw [coarse_capacity_chunks, pow_succ, Nat.mul_comm]

theorem coarseSourceTreeOfList_word_eq {α : Type u} (B D : ℕ) (source : List α)
    (hcapacity : source.length ≤ B ^ D) :
    (coarseSourceTreeOfList B D source).word = source := by
  rw [coarseSourceTreeOfList_word, List.take_of_length_le hcapacity]

/-- A real target character is present at its framed before index. -/
theorem coarseTargetFrame_prefix_get {α : Type u} (k : ℕ)
    (before suffix : List α) (letter : α) :
    (coarseTargetFrame k (before ++ letter :: suffix))[k + before.length]?.getD none = some letter := by
  rw [coarseTargetFrame, List.getElem?_append_left (by simp)]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_replicate, Nat.add_sub_cancel_left, List.getElem?_map]
  rw [List.getElem?_append_right (by omega)]
  simp

/-- Advancing an actual alignment cut gives a legal bounded shift. The
only budget is its preceding displacement plus its remaining edit cost. -/
theorem coarse_anchor_advance (k start before : ℕ) (shift : Fin (2 * k + 1))
    (sourceWidth targetWidth cutCost remaining : ℕ)
    (hanchor : start + shift.val = k + before)
    (hbudget : Nat.dist start before + (cutCost + remaining) ≤ k)
    (hsource : sourceWidth ≤ targetWidth + cutCost)
    (htarget : targetWidth ≤ sourceWidth + cutCost) :
    ∃ next : Fin (2 * k + 1),
      start + sourceWidth + next.val = k + (before + targetWidth) ∧
      Nat.dist shift.val next.val ≤ cutCost ∧
      Nat.dist (start + sourceWidth) (before + targetWidth) + remaining ≤ k := by
  let code := k + (before + targetWidth) - (start + sourceWidth)
  have hcode : code < 2 * k + 1 := by
    dsimp [code]
    simp only [Nat.dist] at hbudget
    omega
  refine ⟨⟨code, hcode⟩, ?_, ?_, ?_⟩
  all_goals
    simp only [Nat.dist, code] at *
    omega

/-- Exact first-child alignment cost controls every actual shift-tree
leaf; no leaf correspondence oracle is assumed. -/
theorem coarse_leaf_edit_upper {B : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (target before piece suffix : List α) (letter : Option α)
    (start : ℕ) (shift : Fin (2 * k + 1))
    (htarget : target = before ++ piece ++ suffix)
    (hanchor : start + shift.val = k + before.length) :
    coarseShiftCost k (coarseTargetFrame k target) (.leaf (B := B) letter) start shift ≤
      edit (CoarseSourceTree.leaf (B := B) letter).word piece := by
  cases letter with
  | none => simp only [coarseShiftCost]; exact Nat.zero_le _
  | some letter =>
    by_cases hzero : edit [letter] piece = 0
    · have heq : [letter] = piece := (cost_eq_zero_iff (s := true)).mp hzero
      rw [← heq] at htarget
      subst target
      simp only [List.append_assoc, List.singleton_append, coarseShiftCost, hanchor,
        coarseTargetFrame_prefix_get, ↓reduceIte]
      exact Nat.zero_le _
    · have hpositive : 1 ≤ edit [letter] piece := by omega
      simp only [coarseShiftCost, CoarseSourceTree.word, Option.toList_some]
      split_ifs <;> omega

/-- Recursive actual optimal cuts bound child minima. The explicit
before allowance accounts for the displacement from the parent's shift. -/
theorem coarseChildrenCost_edit_upper {B D : ℕ} {α : Type u}
    (k : ℕ) (target : List α) (C : ℕ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : List (CoarseSourceTree B α D))
    (hchild : ∀ child ∈ children, ∀ (before piece suffix : List α) start shift,
      target = before ++ piece ++ suffix →
      start + shift.val = k + before.length →
      Nat.dist start before.length + edit child.word piece ≤ k →
      value child start shift ≤ C * edit child.word piece)
    (before piece suffix : List α) (start : ℕ)
    (parent anchor : Fin (2 * k + 1)) (allowance : ℕ)
    (htarget : target = before ++ piece ++ suffix)
    (hanchor : start + anchor.val = k + before.length)
    (hbudget : Nat.dist start before.length +
      edit (children.map CoarseSourceTree.word).flatten piece ≤ k)
    (hallowance : Nat.dist parent.val anchor.val ≤ allowance) :
    coarseChildrenCost k value children start parent ≤
      C * edit (children.map CoarseSourceTree.word).flatten piece +
        2 * children.length * (allowance + edit (children.map CoarseSourceTree.word).flatten piece) := by
  induction children generalizing before piece suffix start anchor allowance with
  | nil => simp only [coarseChildrenCost, List.length_nil, mul_zero, zero_mul, add_zero]; exact Nat.zero_le _
  | cons child rest ih =>
    obtain ⟨left, right, hlocal, hsplit⟩ := edit_append_split child.word
      (rest.map CoarseSourceTree.word).flatten piece
    have hsplit' : edit ((child :: rest).map CoarseSourceTree.word).flatten piece =
        edit child.word left + edit (rest.map CoarseSourceTree.word).flatten right := by
      simpa only [List.map_cons, List.flatten_cons] using hsplit
    have hfirst := hchild child (by simp) before left (right ++ suffix) start anchor
      (by simpa only [hlocal, List.append_assoc] using htarget) hanchor
      (by rw [hsplit'] at hbudget; omega)
    obtain ⟨hsource, htargetWidth⟩ := cost_length_bounds (s := true) child.word left
    change child.word.length ≤ left.length + edit child.word left at hsource
    change left.length ≤ child.word.length + edit child.word left at htargetWidth
    obtain ⟨next, hnext, hmove, hremaining⟩ := coarse_anchor_advance k start before.length anchor
      child.word.length left.length (edit child.word left)
      (edit (rest.map CoarseSourceTree.word).flatten right) hanchor
      (by simpa only [hsplit'] using hbudget) hsource htargetWidth
    have hnextAllowance : Nat.dist parent.val next.val ≤ allowance + edit child.word left :=
      (Nat.dist.triangle_inequality parent.val anchor.val next.val).trans
        (Nat.add_le_add hallowance hmove)
    have hrest := ih (fun next hnext => hchild next (by simp [hnext]))
      (before ++ left) right suffix (start + child.word.length) next
      (allowance + edit child.word left)
      (by simpa only [hlocal, List.append_assoc] using htarget)
      (by simpa only [List.length_append] using hnext)
      (by simpa only [List.length_append] using hremaining) hnextAllowance
    have hminimum := inf'_le (fun next => value child start next + 2 * Nat.dist parent.val next.val)
      (mem_univ anchor)
    have hfirstBound : univ.inf' univ_nonempty
        (fun next => value child start next + 2 * Nat.dist parent.val next.val) ≤
        C * edit child.word left + 2 * allowance :=
      hminimum.trans (Nat.add_le_add hfirst (Nat.mul_le_mul_left 2 hallowance))
    simp only [coarseChildrenCost, List.length_cons, hsplit']
    have hsum := Nat.add_le_add hfirstBound hrest
    nlinarith

/-- The actual bounded-shift recurrence is at most the manuscript's
linear-in-depth distortion, using optimal unrestricted edit scripts. -/
theorem coarseShiftCost_edit_upper {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (target : List α) (tree : CoarseSourceTree B α D)
    (before piece suffix : List α) (start : ℕ) (shift : Fin (2 * k + 1))
    (htarget : target = before ++ piece ++ suffix)
    (hanchor : start + shift.val = k + before.length)
    (hbudget : Nat.dist start before.length + edit tree.word piece ≤ k) :
    coarseShiftCost k (coarseTargetFrame k target) tree start shift ≤
      (1 + 2 * B * D) * edit tree.word piece := by
  induction tree generalizing before piece suffix start shift with
  | leaf letter =>
    simpa only [mul_zero, add_zero, one_mul] using
      coarse_leaf_edit_upper k target before piece suffix letter start shift htarget hanchor
  | @branch D children ih =>
    have hword : (List.ofFn children).map CoarseSourceTree.word =
        List.ofFn (fun i => (children i).word) := by
      simp only [List.map_ofFn, Function.comp_def]
    have hbound := coarseChildrenCost_edit_upper k target (1 + 2 * B * D)
      (fun child => coarseShiftCost k (coarseTargetFrame k target) child) (List.ofFn children)
      (by
        intro child hchild before piece suffix start shift htarget hanchor hbudget
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchild
        exact ih i before piece suffix start shift htarget hanchor hbudget)
      before piece suffix start shift shift 0 htarget hanchor
      (by simpa only [hword, CoarseSourceTree.word] using hbudget) (by simp)
    simp only [CoarseSourceTree.word, coarseShiftCost, hword, List.length_ofFn,
      zero_add] at hbound ⊢
    nlinarith

/-- Section 3's second deterministic distortion inequality for the
executable finite coarse tree, conditional only on the guessed distance. -/
theorem coarseTreeValue_edit_upper {B D : ℕ} {α : Type u} [DecidableEq α]
    (tree : CoarseSourceTree B α D) (target : List α) (k : ℕ)
    (hguess : edit tree.word target ≤ k) :
    coarseTreeValue tree target k ≤ (1 + 2 * B * D) * edit tree.word target := by
  exact coarseShiftCost_edit_upper k target tree [] target [] 0 (coarseRootShift k)
    (by simp) (by simp [coarseRootShift]) (by simpa using hguess)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Seed
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Threshold reconstruction in the initial estimator

Deterministic reconstruction from Section 3 of the September 24, 2026
edit-distance manuscript.  Concentration is kept separate: the thresholds
can influence the approximate child costs, so no independence assumption
about those approximate costs is made here.
-/

namespace EditApproximation

theorem thresholdContribution_nonneg {threshold scale value : ℝ} (hscale : 0 ≤ scale) :
    0 ≤ thresholdContribution threshold scale value := by
  unfold thresholdContribution
  split_ifs
  · exact hscale.trans (le_max_right _ _)
  · rfl

theorem thresholdContribution_mono {threshold scale value value' : ℝ}
    (hscale : 0 ≤ scale) (hle : value ≤ value') :
    thresholdContribution threshold scale value ≤
      thresholdContribution threshold scale value' := by
  unfold thresholdContribution
  split_ifs with h h'
  · exact max_le_max hle le_rfl
  · exact False.elim (h' (h.trans hle))
  · exact hscale.trans (le_max_right _ _)
  · rfl

/-- Pathwise threshold sandwich. In particular, `estimate` may depend on
`threshold`; the proof only uses its two deterministic error bounds. -/
theorem threshold_sandwich {threshold scale estimate lower upper lam : ℝ}
    (hscale : 0 ≤ scale) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hlower : (1 + lam) * lower - lam * threshold ≤ estimate)
    (hupper : estimate ≤ (1 - lam) * upper + lam * threshold) :
    thresholdContribution threshold scale lower ≤
        thresholdContribution threshold scale estimate ∧
      thresholdContribution threshold scale estimate ≤
        thresholdContribution threshold scale upper := by
  constructor
  · by_cases hlt : threshold ≤ lower
    · have hprod := mul_nonneg hlam (sub_nonneg.mpr hlt)
      have hle : lower ≤ estimate := by nlinarith
      exact thresholdContribution_mono hscale hle
    · simp only [thresholdContribution, ite_eq_right hlt]
      exact thresholdContribution_nonneg hscale
  · by_cases hlt : threshold ≤ estimate
    · have hprod := mul_le_mul_of_nonneg_left hlt hlam
      have hle : estimate ≤ upper := by nlinarith
      exact thresholdContribution_mono hscale hle
    · simp only [thresholdContribution, ite_eq_right hlt]
      exact thresholdContribution_nonneg hscale

/-- The precise factors used in the manuscript's threshold sandwich. -/
theorem coarse_threshold_sandwich {threshold scale estimate trueCost f lam : ℝ}
    (hscale : 0 ≤ scale) (hf : 0 < f) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hlower : trueCost / f - lam * threshold ≤ estimate)
    (hupper : estimate ≤ f * trueCost + lam * threshold) :
    thresholdContribution threshold scale (trueCost / (f * (1 + lam))) ≤
        thresholdContribution threshold scale estimate ∧
      thresholdContribution threshold scale estimate ≤
        thresholdContribution threshold scale (f * trueCost / (1 - lam)) := by
  apply threshold_sandwich hscale hlam hlamone
  · have hid : (1 + lam) * (trueCost / (f * (1 + lam))) = trueCost / f := by
      field_simp
    simpa only [hid] using hlower
  · have hid : (1 - lam) * (f * trueCost / (1 - lam)) = f * trueCost := by
      field_simp [ne_of_gt (sub_pos.mpr hlamone)]
    simpa only [hid] using hupper

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The concrete pruned coarse estimator

The random labels are a finite complete tree of integers in `1,...,B`.
Every execution below uses rational arithmetic and literal finite minima;
pruned arrays are represented by the zero function. Accuracy events are
kept separate from this executable definition.
-/

namespace EditApproximation

open Finset

universe u

/- All threshold labels, including labels below nodes which may be pruned. -/


/-- Rational version of the literal threshold contribution. -/


theorem coarseThresholdContribution_cast (threshold scale value : ℚ) :
    (coarseThresholdContribution threshold scale value : ℝ) =
      thresholdContribution threshold scale value := by
  by_cases h : threshold ≤ value
  · have hreal : (threshold : ℝ) ≤ value := by exact_mod_cast h
    simp only [coarseThresholdContribution, thresholdContribution, h, hreal,
      ↓reduceIte, Rat.cast_max]
  · have hreal : ¬(threshold : ℝ) ≤ value := by exact_mod_cast h
    simp only [coarseThresholdContribution, thresholdContribution, h, hreal,
      ↓reduceIte, Rat.cast_zero]


/-- Section 3's pruned rational recurrence. All labels are supplied
beforehand; execution exposes a label only when its parent is expanded. -/


theorem coarseChildThreshold_nonneg {B : ℕ} {Q allowance : ℚ} (draw : Fin B)
    (hQ : 0 ≤ Q) (ha : 0 ≤ allowance) : 0 ≤ coarseChildThreshold B Q allowance draw := by
  unfold coarseChildThreshold
  positivity

theorem coarseChildThreshold_pos {B : ℕ} {Q allowance : ℚ} (draw : Fin B)
    (hQ : 0 < Q) (ha : 0 < allowance) : 0 < coarseChildThreshold B Q allowance draw := by
  have hB : 0 < B := Nat.zero_lt_of_lt draw.isLt
  unfold coarseChildThreshold
  positivity

/-- Adding a nonnegative connection penalty and taking the actual
finite minimum preserves the multiplicative/additive child guarantee. -/
theorem coarse_penalty_minimum_error {ι : Type*} [Fintype ι] [Nonempty ι]
    (trueCost penalty : ι → ℕ) (estimate : ι → ℚ) (f error : ℝ)
    (hf : 1 ≤ f)
    (hlower : ∀ i, (trueCost i : ℝ) / f - error ≤ estimate i)
    (hupper : ∀ i, (estimate i : ℝ) ≤ f * trueCost i + error) :
    ((univ.inf' univ_nonempty (fun i => trueCost i + penalty i) : ℕ) : ℝ) / f - error ≤
        ((univ.inf' univ_nonempty (fun i => estimate i + (penalty i : ℚ)) : ℚ) : ℝ) ∧
      ((univ.inf' univ_nonempty (fun i => estimate i + (penalty i : ℚ)) : ℚ) : ℝ) ≤
        f * ((univ.inf' univ_nonempty (fun i => trueCost i + penalty i) : ℕ) : ℝ) + error := by
  have hfpos : 0 < f := lt_of_lt_of_le zero_lt_one hf
  constructor
  · obtain ⟨i, hi, hmin⟩ := exists_mem_eq_inf' (s := univ) univ_nonempty
      (fun i => estimate i + (penalty i : ℚ))
    rw [hmin]
    have htrue : ((univ.inf' univ_nonempty (fun i => trueCost i + penalty i) : ℕ) : ℝ) ≤
        (trueCost i : ℝ) + penalty i := by
      exact_mod_cast inf'_le (fun i => trueCost i + penalty i) hi
    have hpen : (penalty i : ℝ) / f ≤ penalty i := by
      apply (div_le_iff₀ hfpos).2
      nlinarith [show (0 : ℝ) ≤ penalty i by positivity]
    simp only [Rat.cast_add, Rat.cast_natCast]
    calc
      _ ≤ ((trueCost i : ℝ) + penalty i) / f - error :=
        sub_le_sub_right (div_le_div_of_nonneg_right htrue hfpos.le) _
      _ = (trueCost i : ℝ) / f - error + (penalty i : ℝ) / f := by ring
      _ ≤ _ := add_le_add (hlower i) hpen
  · obtain ⟨i, hi, hmin⟩ := exists_mem_eq_inf' (s := univ) univ_nonempty
      (fun i => trueCost i + penalty i)
    rw [hmin]
    have hestimate : ((univ.inf' univ_nonempty (fun i => estimate i + (penalty i : ℚ)) : ℚ) : ℝ) ≤
        (estimate i : ℝ) + penalty i := by
      exact_mod_cast inf'_le (fun i => estimate i + (penalty i : ℚ)) hi
    simp only [Nat.cast_add]
    exact hestimate.trans (by nlinarith [hupper i, show (0 : ℝ) ≤ penalty i by positivity])

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseAccuracy
attribute [-instance] _root_.OAI.EditApproximation.coarseDrawMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.coarseDrawsFintype _root_.OAI.EditApproximation.coarseDrawsInhabited _root_.OAI.EditApproximation.coarseDrawsMeasurableSingletonClass _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.coarseInitialMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Pathwise accuracy of the concrete coarse recurrence

The events concern only fixed true child minima sampled with independent
labels. The deterministic reconstruction requires no independence of
approximate child costs.
-/

namespace EditApproximation

open Finset

universe u

/-- The actual rational estimator is trapped between two sums of fixed
true costs, even when each child estimate depends on its threshold. -/
theorem coarseThresholdChildrenCost_sandwich {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (allowance : ℚ) (f : ℝ)
    (hQ : 0 ≤ Q) (ha : 0 ≤ allowance) (hf : 1 ≤ f)
    (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (start : ℕ) (shift : Fin (2 * k + 1))
    (hchild : CoarseChildAccuracy k Q lam trueValue value allowance f children start) :
    coarseTrueThresholdSum k Q trueValue allowance
        (fun cost => cost / (f * (1 + (lam : ℝ)))) children start shift ≤
      ((coarseThresholdChildrenCost k Q lam value allowance children start shift : ℚ) : ℝ) ∧
    ((coarseThresholdChildrenCost k Q lam value allowance children start shift : ℚ) : ℝ) ≤
      coarseTrueThresholdSum k Q trueValue allowance
        (fun cost => f * cost / (1 - (lam : ℝ))) children start shift := by
  induction children generalizing start with
  | nil => simp only [coarseTrueThresholdSum, coarseThresholdChildrenCost, Rat.cast_zero]; exact ⟨le_rfl, le_rfl⟩
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have hminimum := coarse_penalty_minimum_error (trueValue child start)
      (fun next => 2 * Nat.dist shift.val next.val)
      (value child below (lam * coarseChildThreshold B Q allowance draw) start)
      f ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ) hf
      (fun next => (hchild.1 next).1)
      (fun next => (hchild.1 next).2)
    have hfpos : 0 < f := lt_of_lt_of_le zero_lt_one hf
    have hscale : (0 : ℝ) ≤ ((allowance / Q : ℚ) : ℝ) := by exact_mod_cast div_nonneg ha hQ
    have hstep := coarse_threshold_sandwich hscale hfpos
      (by exact_mod_cast hlam : (0 : ℝ) ≤ lam)
      (by exact_mod_cast hlamone : (lam : ℝ) < 1)
      (by simpa only [Rat.cast_mul] using hminimum.1)
      (by simpa only [Rat.cast_mul] using hminimum.2)
    have hrest := ih (start + child.word.length) hchild.2
    simp only [coarseThresholdChildrenCost, coarseTrueThresholdSum,
      Rat.cast_add, coarseThresholdContribution_cast, Rat.cast_div]
    simp only [Rat.cast_div] at hstep
    exact ⟨add_le_add hstep.1 hrest.1, add_le_add hstep.2 hrest.2⟩

/-- Combining the true-cost concentration events gives the exact
structural-factor update for the executable rational child traversal. -/
theorem coarseThresholdChildrenCost_reconstruction {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (allowance : ℚ) (f : ℝ)
    (hQ : 0 ≤ Q) (ha : 0 ≤ allowance) (hf : 1 ≤ f)
    (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (start : ℕ) (shift : Fin (2 * k + 1))
    (hchild : CoarseChildAccuracy k Q lam trueValue value allowance f children start)
    (hconcentrationLower :
      (1 - (lam : ℝ)) *
        (((coarseChildrenCost k trueValue (children.map Prod.fst) start shift : ℕ) : ℝ) /
          (f * (1 + (lam : ℝ)))) - allowance ≤
        coarseTrueThresholdSum k Q trueValue allowance
          (fun cost => cost / (f * (1 + (lam : ℝ)))) children start shift)
    (hconcentrationUpper :
      coarseTrueThresholdSum k Q trueValue allowance
          (fun cost => f * cost / (1 - (lam : ℝ))) children start shift ≤
        (1 + (lam : ℝ)) *
          (f * ((coarseChildrenCost k trueValue (children.map Prod.fst) start shift : ℕ) : ℝ) /
            (1 - (lam : ℝ))) + allowance) :
    ((coarseChildrenCost k trueValue (children.map Prod.fst) start shift : ℕ) : ℝ) /
        (f * (1 + (lam : ℝ)) / (1 - (lam : ℝ))) - allowance ≤
      ((coarseThresholdChildrenCost k Q lam value allowance children start shift : ℚ) : ℝ) ∧
    ((coarseThresholdChildrenCost k Q lam value allowance children start shift : ℚ) : ℝ) ≤
      (f * (1 + (lam : ℝ)) / (1 - (lam : ℝ))) *
        ((coarseChildrenCost k trueValue (children.map Prod.fst) start shift : ℕ) : ℝ) + allowance := by
  have hsandwich := coarseThresholdChildrenCost_sandwich k Q lam trueValue value children allowance f
    hQ ha hf hlam hlamone start shift hchild
  have hfpos : 0 < f := lt_of_lt_of_le zero_lt_one hf
  have hl : (lam : ℝ) < 1 := by exact_mod_cast hlamone
  have hlnonnegative : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlower := hconcentrationLower.trans hsandwich.1
  have hupper := hsandwich.2.trans hconcentrationUpper
  constructor
  · convert hlower using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  · convert hupper using 1
    all_goals try with_reducible_and_instances rfl
    ring

theorem coarseStructuralFactor_one_le (lam : ℚ) (D : ℕ)
    (hlam : 0 ≤ lam) (hlamone : lam < 1) : 1 ≤ coarseStructuralFactor lam D := by
  have hl : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlone : (lam : ℝ) < 1 := by exact_mod_cast hlamone
  apply one_le_pow₀
  apply (le_div_iff₀ (sub_pos.mpr hlone)).2
  nlinarith

theorem coarseStructuralFactor_succ (lam : ℚ) (D : ℕ) :
    coarseStructuralFactor lam (D + 1) =
      coarseStructuralFactor lam D * (1 + (lam : ℝ)) / (1 - (lam : ℝ)) := by
  simp only [coarseStructuralFactor, pow_succ]
  ring

theorem CoarseDescendantEvents.to_accuracy {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam allowance : ℚ) (f : ℝ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (event : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Prop)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (hchild : ∀ child draw below, (child, draw, below) ∈ children → ∀ start,
      event child below (lam * coarseChildThreshold B Q allowance draw) start → ∀ shift,
        (trueValue child start shift : ℝ) / f -
          ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ) ≤
            value child below (lam * coarseChildThreshold B Q allowance draw) start shift ∧
        (value child below (lam * coarseChildThreshold B Q allowance draw) start shift : ℝ) ≤
          f * trueValue child start shift + ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ))
    (start : ℕ) (hevent : CoarseDescendantEvents Q lam allowance event children start) :
    CoarseChildAccuracy k Q lam trueValue value allowance f children start := by
  induction children generalizing start with
  | nil => trivial
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    exact ⟨hchild child draw below (by simp) start hevent.1,
      ih (fun child draw below hmem => hchild child draw below (by simp [hmem]))
        (start + child.word.length) hevent.2⟩

/-- On the concrete true-cost event, the literal rational pruned
estimator has exactly the claimed depth-dependent error at every shift. -/
theorem coarseThresholdEstimate_accurate {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α))
    (tree : CoarseSourceTree B α D) (draws : CoarseThresholdDraws B D)
    (allowance : ℚ) (start : ℕ)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam < 1) (ha : 0 ≤ allowance)
    (hevent : CoarseAccuracyEvent k Q lam frame tree draws allowance start) :
    ∀ shift : Fin (2 * k + 1),
      (coarseShiftCost k frame tree start shift : ℝ) / coarseStructuralFactor lam D - allowance ≤
          coarseThresholdEstimate k Q lam frame tree draws allowance start shift ∧
      (coarseThresholdEstimate k Q lam frame tree draws allowance start shift : ℝ) ≤
        coarseStructuralFactor lam D * coarseShiftCost k frame tree start shift + allowance := by
  induction tree generalizing allowance start with
  | leaf letter =>
    intro shift
    have haReal : (0 : ℝ) ≤ allowance := by exact_mod_cast ha
    simp only [coarseThresholdEstimate, coarseStructuralFactor, pow_zero, div_one, one_mul]
    split_ifs with hprune
    · have hwidth := coarseShiftCost_le_width k frame (.leaf (B := B) letter) start shift
      have hwidthQ : (coarseShiftCost k frame (.leaf (B := B) letter) start shift : ℚ) ≤
          (CoarseSourceTree.leaf (B := B) letter).word.length := by exact_mod_cast hwidth
      have hwidthReal : (coarseShiftCost k frame (.leaf (B := B) letter) start shift : ℝ) ≤ allowance := by
        exact_mod_cast hwidthQ.trans hprune
      simp only [Rat.cast_zero]
      constructor <;> linarith [show (0 : ℝ) ≤ coarseShiftCost k frame (.leaf (B := B) letter) start shift by positivity]
    · simp only [Rat.cast_natCast]
      constructor <;> linarith
  | @branch D children ih =>
    obtain ⟨draws, below⟩ := draws
    have hfactor := coarseStructuralFactor_one_le lam (D + 1) hlam hlamone
    have hfactorPos : 0 < coarseStructuralFactor lam (D + 1) := lt_of_lt_of_le zero_lt_one hfactor
    have haReal : (0 : ℝ) ≤ allowance := by exact_mod_cast ha
    intro shift
    by_cases hprune : ((CoarseSourceTree.branch children).word.length : ℚ) ≤ allowance
    · simp only [coarseThresholdEstimate, hprune, ↓reduceIte, Rat.cast_zero]
      have hwidth := coarseShiftCost_le_width k frame (.branch children) start shift
      have hwidthQ : (coarseShiftCost k frame (.branch children) start shift : ℚ) ≤
          (CoarseSourceTree.branch children).word.length := by exact_mod_cast hwidth
      have hwidthReal : (coarseShiftCost k frame (.branch children) start shift : ℝ) ≤ allowance := by
        exact_mod_cast hwidthQ.trans hprune
      have htrueNonnegative : (0 : ℝ) ≤ coarseShiftCost k frame (.branch children) start shift := by positivity
      have hdiv : (coarseShiftCost k frame (.branch children) start shift : ℝ) /
          coarseStructuralFactor lam (D + 1) ≤ coarseShiftCost k frame (.branch children) start shift := by
        apply (div_le_iff₀ hfactorPos).2
        nlinarith
      exact ⟨by linarith, by positivity⟩
    · have hdescendant := hevent.1
      have hchildAccuracy := CoarseDescendantEvents.to_accuracy k Q lam allowance
        (coarseStructuralFactor lam D) (fun child => coarseShiftCost k frame child)
        (fun child => coarseThresholdEstimate k Q lam frame child)
        (fun child => CoarseAccuracyEvent k Q lam frame child)
        (List.ofFn fun i => (children i, draws i, below i))
        (by
          intro child draw childBelow hmem childStart hchildEvent
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact ih i (below i) _ childStart
            (mul_nonneg hlam (coarseChildThreshold_nonneg (draws i) hQ ha)) hchildEvent)
        start hdescendant
      have hstep := coarseThresholdChildrenCost_reconstruction k Q lam
        (fun child => coarseShiftCost k frame child)
        (fun child => coarseThresholdEstimate k Q lam frame child)
        (List.ofFn fun i => (children i, draws i, below i)) allowance
        (coarseStructuralFactor lam D) hQ ha (coarseStructuralFactor_one_le lam D hlam hlamone)
        hlam hlamone start shift hchildAccuracy (hevent.2 shift).1 (hevent.2 shift).2
      simpa only [coarseThresholdEstimate, hprune, ↓reduceIte, List.map_ofFn,
        Function.comp_def, coarseShiftCost, coarseStructuralFactor_succ] using hstep

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BalancedWidths
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.treeLayerCodeWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Width and node counts for the fixed interval tree

Repeated ceiling division gives the physical-depth width bound. This
includes empty children and repeated interval labels, which must still
be counted as distinct nodes in the lazy evaluation analysis.
-/

namespace EditApproximation

open Finset

theorem treeLayer_card (M d : ℕ) : Fintype.card (TreeLayer M d) = M ^ d := by
  induction d with
  | zero =>
    change Fintype.card PUnit = 1
    exact Fintype.card_punit
  | succ d ih =>
    change Fintype.card (TreeLayer M d × Fin M) = M ^ (d + 1)
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]

theorem complete_tree_node_count (M J : ℕ) (hM : 2 ≤ M) :
    (∑ d ∈ range (J + 1), Fintype.card (TreeLayer M d)) ≤ 2 * M ^ J := by
  simp_rw [treeLayer_card]
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, pow_succ]
    have hmul := Nat.mul_le_mul_right (M ^ J) hM
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem coarseExponent_maximal (ell p : ℕ) (hp : p ^ 4 ≤ Nat.log 2 ell) :
    p ≤ coarseExponent ell := by
  apply Nat.le_sqrt'.2
  apply Nat.le_sqrt'.2
  simpa only [← pow_mul] using hp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Depth of the computed interval tree

The branching factor is the power of two prescribed by the algorithm.
Ceiling logarithms count physical levels, including empty intervals.
-/

namespace EditApproximation

open Finset



theorem intervalTreeDepth_power_le (M nx : ℕ) (hM : 2 ≤ M) :
    M ^ intervalTreeDepth M nx ≤ M * max 1 nx := by
  by_cases hx : max 1 nx = 1
  · have hz : Nat.clog M 1 = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact (Nat.clog_le_iff_le_pow hM).2 (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [intervalTreeDepth, hx, hz, pow_zero, mul_one] using
      (by omega : 1 ≤ M)
  · have hx1 : 1 < max 1 nx := by omega
    have hdepth := Nat.clog_pos hM hx1
    have hpred := Nat.pow_pred_clog_lt_self hM hx1
    unfold intervalTreeDepth
    rw [← Nat.succ_pred_eq_of_pos hdepth,
      pow_succ]
    nlinarith

theorem computed_branching_bounds (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    2 ≤ (integerParameters N).M ∧
      inputSmallLog N ≤ 50 * (heightExponent N / 20) ∧
      heightExponent N / 20 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hquot := Nat.mod_lt (heightExponent N) (by decide : 0 < 20)
  have hsplit := Nat.mod_add_div (heightExponent N) 20
  have hk : 1 ≤ heightExponent N / 20 := by omega
  have hpow : 2 ≤ 2 ^ (heightExponent N / 20) := by
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
  have hexp : heightExponent N ≤ inputHeight N := by
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact ⟨hpow, by omega, (Nat.div_le_self _ _).trans hexp⟩

theorem intervalTreeDepth_node_count (M nx : ℕ) (hM : 2 ≤ M) :
    (∑ d ∈ range (intervalTreeDepth M nx + 1), Fintype.card (TreeLayer M d)) ≤
      2 * M * max 1 nx := by
  have hnodes := complete_tree_node_count M (intervalTreeDepth M nx) hM
  have hcapacity := intervalTreeDepth_power_le M nx hM
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DomainCounts
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counting the actual labeled state domain

The count includes repeated interval labels at different physical nodes.
It bounds simultaneous seed/amplification events without identifying those
nodes or replacing the finite target-state loops by an oracle.
-/

namespace EditApproximation

open Finset

theorem targetStates_length_le (n : ℕ) : (targetStates n).length ≤ (n + 1) ^ 2 := by
  unfold targetStates
  have h := list_flatMap_length_le (List.range (n + 1))
    (fun lo => (List.range (n + 1)).filterMap fun hi => makeTargetState n lo hi)
    (n + 1) (by
      intro lo hlo
      simpa only [List.length_range] using
        List.length_filterMap_le (fun hi => makeTargetState n lo hi) (List.range (n + 1)))
  simpa only [List.length_range, pow_two] using h

theorem labeledStateCount_le (M nx ny : ℕ) (hM : 2 ≤ M) :
    labeledStateCount M nx ny ≤ 2 * M * max 1 nx * (ny + 1) ^ 2 := by
  exact Nat.mul_le_mul (intervalTreeDepth_node_count M nx hM) (targetStates_length_le ny)

theorem computed_labeledStateCount_le (N nx ny : ℕ) (hN : 0 < N)
    (hnx : nx ≤ N) (hny : ny ≤ N) (hell : 200 ≤ inputSmallLog N) :
    labeledStateCount (integerParameters N).M nx ny ≤ 2 ^ (5 * inputHeight N) := by
  have hbranch := computed_branching_bounds N hN hell
  have hM : (integerParameters N).M ≤ 2 ^ inputHeight N :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hbranch.2.2
  have hx : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hy : ny + 1 ≤ 2 ^ inputHeight N :=
    (by omega : ny + 1 ≤ N + 2).trans (inputHeight_covers_length N)
  have hproduct : 2 * (integerParameters N).M * max 1 nx * (ny + 1) ^ 2 ≤
      2 * 2 ^ inputHeight N * 2 ^ inputHeight N * (2 ^ inputHeight N) ^ 2 := by
    gcongr
  have hidentity : 2 * 2 ^ inputHeight N * 2 ^ inputHeight N * (2 ^ inputHeight N) ^ 2 =
      2 ^ (4 * inputHeight N + 1) := by
    rw [← pow_mul]
    conv_lhs => lhs; lhs; lhs; change 2 ^ 1
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have hH : 1 ≤ inputHeight N := Nat.one_le_two_pow
  exact (labeledStateCount_le _ _ _ hbranch.1).trans
    (hproduct.trans (hidentity.le.trans
      (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega))))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarsePadding
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Fresh-symbol right padding

Padding uses `none`, while original letters are tagged by `some`. Removing
the fresh symbols contracts every unrestricted unit-cost edit script.
-/

namespace EditApproximation

open EditDistortion

universe u v

/-- Removing or relabeling letters replaces each edit by at most one edit. -/
theorem step_filterMap_script {α : Type u} {β : Type v} {s : Bool}
    (f : α → Option β) {x y : List α} (step : Step s x y) :
    ∃ n ≤ 1, Script s n (x.filterMap f) (y.filterMap f) := by
  cases step with
  | insert before after letter =>
    cases hletter : f letter with
    | none => exact ⟨0, by omega, by simpa [hletter] using Script.nil ((before ++ after).filterMap f)⟩
    | some b => exact ⟨1, le_rfl, by simpa [hletter] using (Script.single (Step.insert (substitutions := s) (before.filterMap f) (after.filterMap f) b))⟩
  | delete before after letter =>
    cases hletter : f letter with
    | none => exact ⟨0, by omega, by simpa [hletter] using Script.nil ((before ++ after).filterMap f)⟩
    | some b => exact ⟨1, le_rfl, by simpa [hletter] using (Script.single (Step.delete (substitutions := s) (before.filterMap f) (after.filterMap f) b))⟩
  | substitute hs before after a b =>
    cases ha : f a with
    | none =>
      cases hb : f b with
      | none => exact ⟨0, by omega, by simpa [ha, hb] using Script.nil ((before ++ after).filterMap f)⟩
      | some b' => exact ⟨1, le_rfl, by simpa [ha, hb] using (Script.single (Step.insert (substitutions := s) (before.filterMap f) (after.filterMap f) b'))⟩
    | some a' =>
      cases hb : f b with
      | none => exact ⟨1, le_rfl, by simpa [ha, hb] using (Script.single (Step.delete (substitutions := s) (before.filterMap f) (after.filterMap f) a'))⟩
      | some b' => exact ⟨1, le_rfl, by simpa [ha, hb] using (Script.single (Step.substitute hs (before.filterMap f) (after.filterMap f) a' b'))⟩

theorem script_filterMap {α : Type u} {β : Type v} {s : Bool}
    (f : α → Option β) {n : ℕ} {x y : List α} (script : Script s n x y) :
    ∃ m ≤ n, Script s m (x.filterMap f) (y.filterMap f) := by
  induction script with
  | nil word => exact ⟨0, le_rfl, .nil _⟩
  | cons step script ih =>
    obtain ⟨m, hm, hscript⟩ := ih
    obtain ⟨l, hl, hstep⟩ := step_filterMap_script f step
    exact ⟨l + m, by omega, hstep.trans hscript⟩

theorem edit_filterMap_le {α : Type u} {β : Type v}
    (f : α → Option β) (x y : List α) :
    edit (x.filterMap f) (y.filterMap f) ≤ edit x y := by
  obtain ⟨m, hm, hscript⟩ := script_filterMap f (cost_spec (s := true) x y)
  exact (cost_le hscript).trans hm

/-- Right padding to a prescribed common width with a fresh tagged letter. -/


theorem coarsePadTo_length {α : Type u} (n : ℕ) (word : List α) (h : word.length ≤ n) :
    (coarsePadTo n word).length = n := by
  simp only [coarsePadTo, List.length_append, List.length_map, List.length_replicate]
  omega

theorem coarsePadTo_remove {α : Type u} (n : ℕ) (word : List α) :
    (coarsePadTo n word).filterMap id = word := by
  simp [coarsePadTo, List.filterMap_map]

/-- The actual padded instance has distance between the original distance
and twice that distance, including empty and unequal-length inputs. -/
theorem coarsePadding_distance_bounds {α : Type u} (x y : List α) :
    edit x y ≤ edit (coarsePadTo (max x.length y.length) x)
      (coarsePadTo (max x.length y.length) y) ∧
    edit (coarsePadTo (max x.length y.length) x)
      (coarsePadTo (max x.length y.length) y) ≤ 2 * edit x y := by
  constructor
  · have h := edit_filterMap_le id (coarsePadTo (max x.length y.length) x)
      (coarsePadTo (max x.length y.length) y)
    simpa only [coarsePadTo_remove] using h
  · have hlength := cost_length_bounds (s := true) x y
    change x.length ≤ y.length + edit x y ∧ y.length ≤ x.length + edit x y at hlength
    have htail : edit
        (List.replicate (max x.length y.length - x.length) (none : Option α))
        (List.replicate (max x.length y.length - y.length) none) ≤ edit x y := by
      have h := edit_le_max_length
        (List.replicate (max x.length y.length - x.length) (none : Option α))
        (List.replicate (max x.length y.length - y.length) none)
      simp only [List.length_replicate] at h
      rcases le_total x.length y.length with hxy | hyx
      · rw [max_eq_right hxy] at h ⊢
        omega
      · rw [max_eq_left hyx] at h ⊢
        omega
    have hmap := cost_map_le (s := true) some x y
    change edit (x.map some) (y.map some) ≤ edit x y at hmap
    have happend := cost_append_le (s := true) (x.map some) (y.map some)
      (List.replicate (max x.length y.length - x.length) none)
      (List.replicate (max x.length y.length - y.length) none)
    change edit (coarsePadTo (max x.length y.length) x)
      (coarsePadTo (max x.length y.length) y) ≤
        edit (x.map some) (y.map some) +
          edit (List.replicate (max x.length y.length - x.length) none)
            (List.replicate (max x.length y.length - y.length) none) at happend
    exact happend.trans (by omega)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_Concentration
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRange_neZero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coarse threshold concentration from the published scalar input

The quantitative Bernstein bound used in Section 3 does not require
independence of estimated child values.
The random variables to which Bernstein is applied are fixed true-cost
threshold contributions, conditional on ancestor thresholds.
-/

namespace EditApproximation

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Numerical exponent estimate for the coarse estimator's choice of
deviation. The proof also covers the two regimes in the manuscript at once. -/
theorem coarse_bernstein_exponent {lam V allowance scale Q : ℝ}
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1) (hV : 0 ≤ V)
    (ha : 0 < allowance) (hu : 0 < scale) (hQ : Q * scale = allowance) :
    lam * Q / 12 ≤ (lam * V + allowance / 2) ^ 2 /
      (2 * scale * V + (2 / 3 : ℝ) * scale * (lam * V + allowance / 2)) := by
  let z := lam * V + allowance / 2
  have hz : 0 < z := by dsimp [z] <;> positivity
  have ha2 : allowance ≤ 2 * z := by dsimp [z] <;> nlinarith
  have hlamV : lam * V ≤ z := by dsimp [z] <;> linarith
  have hfirst : allowance * (lam * V) ≤ allowance * z :=
    mul_le_mul_of_nonneg_left hlamV ha.le
  have hsecond : lam * (allowance * z) ≤ allowance * z := by
    exact (mul_le_mul_of_nonneg_right hlamone (mul_nonneg ha.le hz.le)).trans_eq
      (one_mul _)
  have hthird : allowance * z ≤ 2 * z ^ 2 := by nlinarith
  have hbase : lam * allowance * (2 * V + (2 / 3 : ℝ) * z) ≤ 12 * z ^ 2 := by
    nlinarith [sq_nonneg z]
  have hdenom : 0 < 2 * scale * V + (2 / 3 : ℝ) * scale * z := by positivity
  apply (le_div_iff₀ hdenom).2
  change lam * Q / 12 * (2 * scale * V + (2 / 3 : ℝ) * scale * z) ≤ z ^ 2
  have heq : lam * Q / 12 * (2 * scale * V + (2 / 3 : ℝ) * scale * z) =
      lam * allowance * (2 * V + (2 / 3 : ℝ) * z) / 12 := by
    rw [← hQ]
    ring
  rw [heq]
  linarith

/-- Coarse threshold concentration, conditional only on the ancestor
data. Its hypotheses specify the centered *true-cost* random variables,
their moment proxy, and the threshold estimator's small bias. -/
theorem coarse_threshold_concentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bernstein : FiniteBernsteinInput μ)
    {n : ℕ} (X : Fin n → Ω → ℝ) (estimator : Ω → ℝ)
    (mean V lam allowance scale Q : ℝ)
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1) (hV : 0 < V)
    (ha : 0 < allowance) (hu : 0 < scale) (hQ : Q * scale = allowance)
    (hscale : scale ≤ allowance / 2)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ scale)
    (hvariance : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) ≤ scale * V)
    (hcenter : ∀ ω, estimator ω - mean = ∑ i, X i ω)
    (hbias : |mean - V| ≤ scale) :
    μ.real {ω | lam * V + allowance < |estimator ω - V|} ≤
      2 * Real.exp (-lam * Q / 12) := by
  let z := lam * V + allowance / 2
  have hz : 0 < z := by dsimp [z] <;> positivity
  have htail := bernstein n X scale (scale * V) z hu (mul_pos hu hV) hz
    hindep hmeas hint hmean hbound hvariance
  have hsubset : {ω | lam * V + allowance < |estimator ω - V|} ⊆
      {ω | z ≤ |∑ i, X i ω|} := by
    intro ω hω
    have htriangle : |estimator ω - V| ≤ |estimator ω - mean| + |mean - V| := by
      calc
        |estimator ω - V| = |(estimator ω - mean) + (mean - V)| := by
          congr 1
          ring
        _ ≤ |estimator ω - mean| + |mean - V| := abs_add_le _ _
    rw [hcenter ω] at htriangle
    change z ≤ |∑ i, X i ω|
    dsimp [z]
    have hω' : lam * V + allowance < |estimator ω - V| := hω
    linarith
  apply (measureReal_mono (μ := μ) hsubset).trans
  apply htail.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hexponent := coarse_bernstein_exponent hlam hlamone hV.le ha hu hQ
  change -z ^ 2 / (2 * (scale * V) + (2 / 3 : ℝ) * scale * z) ≤ -lam * Q / 12
  simpa only [neg_div, neg_mul, mul_assoc] using neg_le_neg hexponent

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteSampling
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniform sampling

The shared group estimator samples child labels uniformly with replacement.
These lemmas use that finite distribution, including its product law;
they do not assume that different group representatives are independent.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem uniform_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (value : ι → ℝ) :
    (∫ i, value i ∂(PMF.uniformOfFintype ι).toMeasure) = uniformMean value := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← mul_sum, uniformMean]
  ring

theorem uniformMean_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (value : ι → ℝ) {bound : ℝ} (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ bound) :
    0 ≤ uniformMean value ∧ uniformMean value ≤ bound := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · exact div_nonneg (sum_nonneg fun i _ => (hvalue i).1) hc.le
  · apply (div_le_iff₀ hc).2
    have hsum := sum_le_sum (s := univ) fun i _ => (hvalue i).2
    simpa only [sum_const, card_univ, nsmul_eq_mul, mul_comm] using hsum

theorem uniform_centered_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (value : ι → ℝ) {bound : ℝ} (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ bound)
    (i : ι) : |value i - uniformMean value| ≤ bound := by
  have hm := uniformMean_bounds value hvalue
  exact abs_le.mpr ⟨by linarith [(hvalue i).1], by linarith [(hvalue i).2]⟩

theorem uniform_centered_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (value : ι → ℝ) :
    (∫ i, (value i - uniformMean value)
      ∂(PMF.uniformOfFintype ι).toMeasure) = 0 := by
  rw [integral_sub (.of_finite) (integrable_const _), uniform_integral, integral_const]
  simp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ThresholdMoments
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Discrete threshold moments

The initial estimator samples an integer uniformly from `1, …, B`.
The finite count below proves its rounding bias exactly; no continuous
threshold distribution is substituted for the executable sampler.
-/

namespace EditApproximation

open Finset

theorem threshold_count (B : ℕ) (scale value : ℝ)
    (hB : 0 < B) (hscale : 0 < scale) (hvalue : 0 ≤ value) (hupper : value < scale) :
    ((Icc 1 B).filter fun (r : ℕ) => scale * (r : ℝ) / B ≤ value).card =
      ⌊(B : ℝ) * value / scale⌋₊ := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hq : 0 ≤ (B : ℝ) * value / scale := by positivity
  have hqB : (B : ℝ) * value / scale < B := by
    apply (div_lt_iff₀ hscale).2
    nlinarith
  have hfloor : ⌊(B : ℝ) * value / scale⌋₊ < B := (Nat.floor_lt hq).2 hqB
  have hiff (r : ℕ) : scale * r / B ≤ value ↔ r ≤ ⌊(B : ℝ) * value / scale⌋₊ := by
    rw [Nat.le_floor_iff hq, div_le_iff₀ hBr, le_div_iff₀ hscale]
    constructor <;> intro h <;> nlinarith
  have hfilter : (Icc 1 B).filter (fun (r : ℕ) => scale * (r : ℝ) / B ≤ value) =
      Icc 1 ⌊(B : ℝ) * value / scale⌋₊ := by
    ext r
    simp only [mem_filter, mem_Icc, hiff]
    constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.trans hfloor.le⟩, h.2⟩
  rw [hfilter]
  simp only [Nat.card_Icc, Nat.add_sub_cancel]

/-- Exact discrete first moment below the scale; dividing the sum by `B`
gives `scale * floor(B * value / scale) / B`. -/
theorem threshold_sum (B : ℕ) (scale value : ℝ)
    (hB : 0 < B) (hscale : 0 < scale) (hvalue : 0 ≤ value) (hupper : value < scale) :
    (∑ r ∈ Icc 1 B, thresholdContribution (scale * r / B) scale value) =
      (⌊(B : ℝ) * value / scale⌋₊ : ℝ) * scale := by
  have hpoint (r : ℕ) : thresholdContribution (scale * r / B) scale value =
      if scale * r / B ≤ value then scale else 0 := by
    simp only [thresholdContribution, max_eq_right hupper.le]
  simp_rw [hpoint]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul,
    threshold_count B scale value hB hscale hvalue hupper]

/-- Bias bound used in the coarse estimator: the discrete mean is below
the true argument by at most one grid unit. -/
theorem threshold_bias (B : ℕ) (scale value : ℝ)
    (hB : 0 < B) (hscale : 0 < scale) (hvalue : 0 ≤ value) (hupper : value < scale) :
    0 ≤ value - (∑ r ∈ Icc 1 B,
      thresholdContribution (scale * r / B) scale value) / B ∧
    value - (∑ r ∈ Icc 1 B,
      thresholdContribution (scale * r / B) scale value) / B ≤ scale / B := by
  rw [threshold_sum B scale value hB hscale hvalue hupper]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hq : 0 ≤ (B : ℝ) * value / scale := by positivity
  have hflo := Nat.floor_le hq
  have hfhi := Nat.lt_floor_add_one ((B : ℝ) * value / scale)
  have hl := (le_div_iff₀ hscale).1 hflo
  have hh := (div_lt_iff₀ hscale).1 hfhi
  constructor
  · apply sub_nonneg.mpr
    exact (div_le_iff₀ hBr).2 (by nlinarith)
  · apply (le_div_iff₀ hBr).2
    have hid : (value - (⌊(B : ℝ) * value / scale⌋₊ : ℝ) * scale / B) * B =
        value * B - (⌊(B : ℝ) * value / scale⌋₊ : ℝ) * scale := by
      field_simp
    rw [hid]
    nlinarith

theorem uniform_centered_square_identity {ι : Type*} (samples : Finset ι)
    (value : ι → ℝ) (hcard : 0 < samples.card) :
    (∑ i ∈ samples, (value i - (∑ j ∈ samples, value j) / samples.card) ^ 2) /
        samples.card =
      (∑ i ∈ samples, value i ^ 2) / samples.card -
        ((∑ i ∈ samples, value i) / samples.card) ^ 2 := by
  let mean := (∑ i ∈ samples, value i) / samples.card
  have hcardr : (0 : ℝ) < samples.card := by exact_mod_cast hcard
  have hexpand : (∑ i ∈ samples, (value i - mean) ^ 2) =
      (∑ i ∈ samples, value i ^ 2) - 2 * mean * (∑ i ∈ samples, value i) +
        (samples.card : ℝ) * mean ^ 2 := by
    calc
      _ = ∑ i ∈ samples, (value i ^ 2 - 2 * mean * value i + mean ^ 2) :=
        sum_congr rfl fun _ _ => by ring
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  change (∑ i ∈ samples, (value i - mean) ^ 2) / samples.card = _
  rw [hexpand]
  dsimp [mean]
  field_simp
  ring

/-- The centered second moment of the actual finite threshold sampler is
at most `scale * value`, as used in the Bernstein variance proxy. -/
theorem threshold_variance_bound (B : ℕ) (scale value : ℝ)
    (hB : 0 < B) (hscale : 0 < scale) (hvalue : 0 ≤ value) (hupper : value < scale) :
    (∑ r ∈ Icc 1 B,
      (thresholdContribution (scale * r / B) scale value -
        (∑ s ∈ Icc 1 B, thresholdContribution (scale * s / B) scale value) / B) ^ 2) / B ≤
      scale * value := by
  have hcard : (Icc 1 B).card = B := by simp only [Nat.card_Icc, Nat.add_sub_cancel]
  have hvariance := uniform_centered_square_identity (Icc 1 B)
    (fun r => thresholdContribution (scale * r / B) scale value) (by omega)
  rw [hcard] at hvariance
  rw [hvariance]
  have hpoint (r : ℕ) : thresholdContribution (scale * r / B) scale value ^ 2 =
      scale * thresholdContribution (scale * r / B) scale value := by
    simp only [thresholdContribution, max_eq_right hupper.le]
    split_ifs <;> ring
  simp_rw [hpoint]
  rw [← mul_sum, mul_div_assoc]
  have hmean := (threshold_bias B scale value hB hscale hvalue hupper).1
  have hscaled := mul_le_mul_of_nonneg_left (sub_nonneg.mp hmean) hscale.le
  nlinarith [sq_nonneg ((∑ r ∈ Icc 1 B,
    thresholdContribution (scale * r / B) scale value) / B)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseSampling
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRange_neZero _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent heterogeneous coarse threshold samples

Every child has its own fixed true cost and an independent uniform label
in `1,...,B`. The child estimates are absent from this probability space:
they enter only the pathwise reconstruction proved separately.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem coarse_sum_labels (B : ℕ) (value : ℕ → ℝ) :
    (∑ draw : Fin B, value (draw.val + 1)) = ∑ r ∈ Icc 1 B, value r := by
  refine sum_bij (fun draw _ => draw.val + 1) ?_ ?_ ?_ ?_
  · intro draw hdraw
    exact mem_Icc.mpr ⟨by omega, by have := draw.isLt; omega⟩
  · intro first hfirst second hsecond hequal
    exact Fin.ext (by omega)
  · intro r hr
    obtain ⟨hlower, hupper⟩ := mem_Icc.mp hr
    refine ⟨⟨r - 1, by omega⟩, mem_univ _, ?_⟩
    change r - 1 + 1 = r
    omega
  · intro draw hdraw
    rfl

theorem coarseThresholdSample_large {B : ℕ} [NeZero B] (scale value : ℝ)
    (hscale : 0 ≤ scale) (hvalue : scale ≤ value) (draw : Fin B) :
    coarseThresholdSample scale value draw = value := by
  have hB : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
  have hdraw : (draw.val + 1 : ℝ) ≤ B := by exact_mod_cast Nat.succ_le_of_lt draw.isLt
  have hthreshold : scale * (draw.val + 1 : ℕ) / B ≤ value := by
    apply le_trans _ hvalue
    apply (div_le_iff₀ hB).2
    exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using hdraw) hscale
  simp only [coarseThresholdSample, thresholdContribution, hthreshold, ↓reduceIte,
    max_eq_left hvalue]

/-- The mean, centered range and variance proxy are established for each
fixed cost, including the deterministic range above the threshold scale. -/
theorem coarseThresholdSample_moments {B : ℕ} [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (scale value : ℝ) (hscale : 0 < scale) (hvalue : 0 ≤ value) :
    (0 ≤ value - uniformMean (coarseThresholdSample (B := B) scale value) ∧
      value - uniformMean (coarseThresholdSample (B := B) scale value) ≤ scale / B) ∧
    (∀ draw : Fin B, |coarseThresholdSample scale value draw -
      uniformMean (coarseThresholdSample (B := B) scale value)| ≤ scale) ∧
    (∫ draw, (coarseThresholdSample scale value draw -
      uniformMean (coarseThresholdSample (B := B) scale value)) ^ 2
      ∂(PMF.uniformOfFintype (Fin B)).toMeasure) ≤ scale * value := by
  have hB : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  by_cases hlarge : scale ≤ value
  · have hconstant : coarseThresholdSample (B := B) scale value = fun _ => value := by
      funext draw
      exact coarseThresholdSample_large scale value hscale.le hlarge draw
    rw [hconstant]
    have hmean : uniformMean (fun _ : Fin B => value) = value := by
      simp only [uniformMean, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    simp only [hmean, sub_self, abs_zero, zero_pow (by decide : 2 ≠ 0), integral_zero]
    exact ⟨⟨le_rfl, div_nonneg hscale.le hBr.le⟩, fun _ => hscale.le,
      mul_nonneg hscale.le hvalue⟩
  · have hsmall : value < scale := lt_of_not_ge hlarge
    have hmean : uniformMean (coarseThresholdSample (B := B) scale value) =
        (∑ r ∈ Icc 1 B, thresholdContribution (scale * r / B) scale value) / B := by
      simp only [uniformMean, Fintype.card_fin, coarseThresholdSample]
      rw [coarse_sum_labels B (fun r => thresholdContribution (scale * r / B) scale value)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hmean]
      exact threshold_bias B scale value hB hscale hvalue hsmall
    · apply uniform_centered_bound
      intro draw
      unfold coarseThresholdSample thresholdContribution
      split_ifs
      · exact ⟨hscale.le.trans (le_max_right _ _), by rw [max_eq_right hsmall.le]⟩
      · exact ⟨le_rfl, hscale.le⟩
    · rw [uniform_integral]
      simp only [uniformMean, Fintype.card_fin, coarseThresholdSample]
      rw [coarse_sum_labels B (fun r => thresholdContribution (scale * r / B) scale value)]
      rw [coarse_sum_labels B (fun r =>
        (thresholdContribution (scale * r / B) scale value -
          (∑ s ∈ Icc 1 B, thresholdContribution (scale * s / B) scale value) / B) ^ 2)]
      exact threshold_variance_bound B scale value hB hscale hvalue hsmall

/-- Actual product-uniform child labels satisfy the manuscript's coarse
Bernstein tail bound for every fixed heterogeneous true-cost list. -/
theorem coarse_product_threshold_concentration_positive {B : ℕ} [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (value : Fin B → ℝ) (scale allowance Q lam : ℝ)
    (hvalue : ∀ i, 0 ≤ value i) (hu : 0 < scale) (ha : 0 < allowance)
    (hQ : Q * scale = allowance) (hscale : scale ≤ allowance / 2)
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1)
    (hV : 0 < ∑ i, value i)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).real
      {draws | lam * (∑ i, value i) + allowance <
        |(∑ i, coarseThresholdSample scale (value i) (draws i)) - ∑ i, value i|} ≤
      2 * Real.exp (-lam * Q / 12) := by
  let μ := (PMF.uniformOfFintype (Fin B)).toMeasure
  let sample := fun i => coarseThresholdSample (B := B) scale (value i)
  let mean := ∑ i, uniformMean (sample i)
  let X : Fin B → (Fin B → Fin B) → ℝ :=
    fun i draws => sample i (draws i) - uniformMean (sample i)
  have hmoments (i : Fin B) := coarseThresholdSample_moments (B := B) scale (value i) hu (hvalue i)
  have hindep : iIndepFun X (Measure.pi fun _ : Fin B => μ) :=
    iIndepFun_pi (μ := fun _ : Fin B => μ)
      (X := fun i draw => sample i draw - uniformMean (sample i))
      (fun _ => (measurable_of_finite _).aemeasurable)
  have hcenter (i : Fin B) : (∫ draws, X i draws ∂Measure.pi (fun _ : Fin B => μ)) = 0 := by
    dsimp [X]
    rw [integral_comp_eval (μ := fun _ : Fin B => μ) (i := i)
      (f := fun draw => sample i draw - uniformMean (sample i))
      (measurable_of_finite _).aestronglyMeasurable]
    exact uniform_centered_integral (sample i)
  have hbound (i : Fin B) : ∀ᵐ draws ∂Measure.pi (fun _ : Fin B => μ), |X i draws| ≤ scale := by
    filter_upwards [] with draws
    exact (hmoments i).2.1 (draws i)
  have hvariance : (∑ i, ∫ draws, (X i draws) ^ 2 ∂Measure.pi (fun _ : Fin B => μ)) ≤
      scale * (∑ i, value i) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    dsimp [X]
    rw [integral_comp_eval (μ := fun _ : Fin B => μ) (i := i)
      (f := fun draw => (sample i draw - uniformMean (sample i)) ^ 2)
      (measurable_of_finite _).aestronglyMeasurable]
    exact (hmoments i).2.2
  have hbias : |mean - ∑ i, value i| ≤ scale := by
    have hnonnegative := sum_nonneg (s := univ) (fun i _ => (hmoments i).1.1)
    have hsum := sum_le_sum (s := univ) (fun i _ => (hmoments i).1.2)
    have hB : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hnonnegative hsum
    have hequal : (B : ℝ) * (scale / B) = scale := by field_simp
    rw [hequal] at hsum
    dsimp [mean]
    rw [abs_of_nonpos (by linarith)]
    linarith
  exact coarse_threshold_concentration (Measure.pi fun _ : Fin B => μ) bernstein X
    (fun draws => ∑ i, sample i (draws i)) mean (∑ i, value i) lam allowance scale Q
    hlam hlamone hV ha hu hQ hscale hindep
    (fun _ => measurable_of_finite _) (fun _ => .of_finite) hcenter hbound hvariance
    (by intro draws; simp only [X, mean, sum_sub_distrib]) hbias

/-- The same exact product-uniform law, including zero total true cost. -/
theorem coarse_product_threshold_concentration {B : ℕ} [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (value : Fin B → ℝ) (scale allowance Q lam : ℝ)
    (hvalue : ∀ i, 0 ≤ value i) (hu : 0 < scale) (ha : 0 < allowance)
    (hQ : Q * scale = allowance) (hscale : scale ≤ allowance / 2)
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).real
      {draws | lam * (∑ i, value i) + allowance <
        |(∑ i, coarseThresholdSample scale (value i) (draws i)) - ∑ i, value i|} ≤
      2 * Real.exp (-lam * Q / 12) := by
  by_cases hV : 0 < ∑ i, value i
  · exact coarse_product_threshold_concentration_positive value scale allowance Q lam
      hvalue hu ha hQ hscale hlam hlamone hV bernstein
  · have htotal : (∑ i, value i) = 0 := by
      have hnonnegative := sum_nonneg (s := univ) (fun i _ => hvalue i)
      linarith
    have hzero (i : Fin B) : value i = 0 := by
      have hi := single_le_sum (s := univ) (fun i _ => hvalue i) (mem_univ i)
      rw [htotal] at hi
      exact le_antisymm hi (hvalue i)
    have hsample (draw : Fin B) : coarseThresholdSample scale 0 draw = 0 := by
      have hB : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
      have hdraw : (0 : ℝ) < (draw.val + 1 : ℕ) := by positivity
      have hthreshold : 0 < scale * (draw.val + 1 : ℕ) / B := by positivity
      simp only [coarseThresholdSample, thresholdContribution, not_le_of_gt hthreshold, ↓reduceIte]
    have hempty : {draws : Fin B → Fin B | lam * (∑ i, value i) + allowance <
        |(∑ i, coarseThresholdSample scale (value i) (draws i)) - ∑ i, value i|} = ∅ := by
      ext draws
      simp only [hzero, hsample, sum_const_zero, mul_zero, zero_add, sub_self, abs_zero,
        not_lt_of_ge ha.le, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    rw [hempty, measureReal_empty]
    positivity

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseProbability
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.coarseInitialMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual finite coarse randomness

At each internal node, the child thresholds are independent uniform labels.
Recursive subtrees are independent of these labels. This complete probability
space also includes labels below pruned nodes.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

universe u

/-- The literal list recurrence equals its finite sum at the actual starts. -/
theorem coarseChildrenCost_eq_sum {B D : ℕ} {α : Type u}
    (k : ℕ) (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : List (CoarseSourceTree B α D)) (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseChildrenCost k value children start shift =
      ∑ i : Fin children.length, univ.inf' univ_nonempty
        (fun next => value children[i.val] (coarseChildListStart children start i) next +
          2 * Nat.dist shift.val next.val) := by
  induction children generalizing start with
  | nil => simp [coarseChildrenCost]
  | cons child rest ih =>
    simp only [List.length_cons]
    rw [coarseChildrenCost, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getElem_cons_zero, coarseChildListStart, List.take_zero,
      List.map_nil, List.flatten_nil, List.length_nil, add_zero, Fin.val_succ,
      List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.flatten_cons,
      List.length_append]
    rw [ih]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp only [coarseChildListStart, Nat.add_assoc]

/-- Integrating a uniform conditional failure bound over the ancestor
labels does not add a union over the possible allowance values. -/
theorem coarse_product_section_bound {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (bad : Set (X × Y)) (hbad : MeasurableSet bad) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hsection : ∀ x, ν.real {y | (x, y) ∈ bad} ≤ failure) :
    (μ.prod ν).real bad ≤ failure := by
  have hENN (x : X) : ν {y | (x, y) ∈ bad} ≤ ENNReal.ofReal failure := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν {y | (x, y) ∈ bad})]
    exact ENNReal.ofReal_le_ofReal (hsection x)
  have hproduct : μ.prod ν bad ≤ ENNReal.ofReal failure := by
    rw [Measure.prod_apply hbad]
    apply (lintegral_mono (fun x => hENN x)).trans_eq
    simp
  exact ENNReal.toReal_le_of_le_ofReal hfailure hproduct

/-- The recursive child coordinates have precisely their own subtree law. -/
theorem coarse_child_projection_probability (B D : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (i : Fin B) (bad : Set (CoarseThresholdDraws B D)) :
    (Measure.pi fun _ : Fin B => coarseDrawMeasure B D).real {below | below i ∈ bad} =
      (coarseDrawMeasure B D).real bad := by
  have hbad : MeasurableSet bad := (Set.toFinite bad).measurableSet
  have hmap := (measurePreserving_eval (μ := fun _ : Fin B => coarseDrawMeasure B D) i).map_eq
  have hpreimage := Measure.map_apply (μ := Measure.pi fun _ : Fin B => coarseDrawMeasure B D)
    (measurable_pi_apply i) hbad
  rw [hmap] at hpreimage
  exact congrArg ENNReal.toReal hpreimage.symm

theorem coarseDescendantEvents_iff {B D : ℕ} {α : Type u}
    (Q lam allowance : ℚ)
    (event : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Prop)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D)) (start : ℕ) :
    CoarseDescendantEvents Q lam allowance event children start ↔
      ∀ i : Fin children.length, event children[i.val].1 children[i.val].2.2
        (lam * coarseChildThreshold B Q allowance children[i.val].2.1)
        (coarseDataListStart children start i) := by
  induction children generalizing start with
  | nil => simp [CoarseDescendantEvents]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    simp only [List.length_cons]
    rw [Fin.forall_fin_succ]
    simp only [CoarseDescendantEvents, Fin.val_zero, List.getElem_cons_zero,
      coarseDataListStart, List.take_zero, List.map_nil, List.flatten_nil, List.length_nil,
      add_zero, Fin.val_succ, List.getElem_cons_succ, List.take_succ_cons,
      List.map_cons, List.flatten_cons, List.length_append]
    rw [ih]
    simp only [coarseDataListStart, Nat.add_assoc]

theorem coarseTrueThresholdSum_eq_sum {B D : ℕ} {α : Type u}
    (k : ℕ) (Q allowance : ℚ) (transform : ℝ → ℝ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseTrueThresholdSum k Q trueValue allowance transform children start shift =
      ∑ i : Fin children.length,
        thresholdContribution (coarseChildThreshold B Q allowance children[i.val].2.1)
          (allowance / Q)
          (transform ((univ.inf' univ_nonempty (fun next =>
            trueValue children[i.val].1 (coarseDataListStart children start i) next +
              2 * Nat.dist shift.val next.val) : ℕ) : ℝ)) := by
  induction children generalizing start with
  | nil => simp [coarseTrueThresholdSum]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    simp only [List.length_cons]
    rw [coarseTrueThresholdSum, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getElem_cons_zero, coarseDataListStart, List.take_zero,
      List.map_nil, List.flatten_nil, List.length_nil, add_zero, Fin.val_succ,
      List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.flatten_cons,
      List.length_append]
    rw [ih]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp only [coarseDataListStart, Nat.add_assoc]

theorem coarseChildrenCost_ofFn {B D : ℕ} {α : Type u}
    (k : ℕ) (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseChildrenCost k value (List.ofFn children) start shift =
      ∑ i : Fin B, coarseNodeChildCost k value children start shift i := by
  rw [coarseChildrenCost_eq_sum]
  apply Fintype.sum_equiv (finCongr (List.length_ofFn (f := children)))
  intro i
  simp only [List.getElem_ofFn, coarseChildListStart, coarseNodeChildCost, coarseNodeChildStart]
  rfl

theorem coarseTrueThresholdSum_ofFn {B D : ℕ} {α : Type u}
    (k : ℕ) (Q allowance : ℚ) (transform : ℝ → ℝ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseTrueThresholdSum k Q value allowance transform
        (List.ofFn fun i => (children i, draws i, below i)) start shift =
      ∑ i : Fin B, thresholdContribution (coarseChildThreshold B Q allowance (draws i))
        (allowance / Q) (transform (coarseNodeChildCost k value children start shift i)) := by
  rw [coarseTrueThresholdSum_eq_sum]
  apply Fintype.sum_equiv (finCongr (List.length_ofFn
    (f := fun i => (children i, draws i, below i))))
  intro i
  simp only [List.getElem_ofFn, coarseDataListStart, coarseNodeChildCost,
    coarseNodeChildStart, List.map_take, List.map_ofFn, Function.comp_def]
  rfl

theorem coarseChildThreshold_cast (B : ℕ) [NeZero B] (Q allowance : ℚ)
    (hQ : Q ≠ 0) (draw : Fin B) :
    (coarseChildThreshold B Q allowance draw : ℝ) =
      ((allowance : ℝ) / Q) * (draw.val + 1 : ℕ) / B := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne B
  simp only [coarseChildThreshold, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
  field_simp

theorem coarseTrueThresholdSum_sample {B D : ℕ} [NeZero B] {α : Type u}
    (k : ℕ) (Q allowance : ℚ) (hQ : Q ≠ 0) (transform : ℝ → ℝ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseTrueThresholdSum k Q value allowance transform
        (List.ofFn fun i => (children i, draws i, below i)) start shift =
      ∑ i : Fin B, coarseThresholdSample ((allowance : ℝ) / Q)
        (transform (coarseNodeChildCost k value children start shift i)) (draws i) := by
  rw [coarseTrueThresholdSum_ofFn]
  apply sum_congr rfl
  intro i hi
  rw [coarseChildThreshold_cast B Q allowance hQ]
  rfl

/-- A finite family of fixed child-cost lists shares the same independent
threshold labels. A union bound needs no independence between the lists. -/
theorem coarse_finite_threshold_simultaneous {B : ℕ} [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    {I : Type*} [Fintype I]
    (value : I → Fin B → ℝ) (scale allowance Q lam : ℝ)
    (hvalue : ∀ i j, 0 ≤ value i j) (hu : 0 < scale) (ha : 0 < allowance)
    (hQ : Q * scale = allowance) (hscale : scale ≤ allowance / 2)
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).real
      {draws | ¬ ∀ i, |(∑ j, coarseThresholdSample scale (value i j) (draws j)) -
          ∑ j, value i j| ≤ lam * (∑ j, value i j) + allowance} ≤
      Fintype.card I * (2 * Real.exp (-lam * Q / 12)) := by
  classical
  let μ := Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure
  let bad (i : I) : Set (Fin B → Fin B) :=
    {draws | lam * (∑ j, value i j) + allowance <
      |(∑ j, coarseThresholdSample scale (value i j) (draws j)) - ∑ j, value i j|}
  have hsubset : {draws | ¬ ∀ i, |(∑ j, coarseThresholdSample scale (value i j) (draws j)) -
      ∑ j, value i j| ≤ lam * (∑ j, value i j) + allowance} ⊆ ⋃ i, bad i := by
    intro draws hdraws
    obtain ⟨i, hi⟩ := not_forall.mp hdraws
    exact Set.mem_iUnion.mpr ⟨i, lt_of_not_ge hi⟩
  calc
    _ ≤ μ.real (⋃ i, bad i) := measureReal_mono hsubset
    _ ≤ ∑ i, μ.real (bad i) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _ : I, 2 * Real.exp (-lam * Q / 12) := by
      apply sum_le_sum
      intro i hi
      exact coarse_product_threshold_concentration (value i) scale allowance Q lam
        (hvalue i) hu ha hQ hscale hlam hlamone bernstein
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]

/-- One complete node event costs four scalar Bernstein tails per shift. -/
theorem coarseNodeDeviationEvent_probability {B D : ℕ} [NeZero B] {α : Type u}
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam allowance : ℚ) (f : ℝ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ)
    (hQ : 2 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (ha : 0 < allowance) (hf : 0 < f)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).real
      {draws | ¬ CoarseNodeDeviationEvent k Q lam allowance f value children start draws} ≤
      4 * (2 * k + 1 : ℕ) * Real.exp (-(lam : ℝ) * Q / 12) := by
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have har : (0 : ℝ) < allowance := by exact_mod_cast ha
  have hlr : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlone : (lam : ℝ) < 1 := by exact_mod_cast hlamone
  have hvalue (index : Fin (2 * k + 1) × Bool) (i : Fin B) :
      0 ≤ coarseNodeSamplingValue k lam f value children start index i := by
    simp only [coarseNodeSamplingValue]
    split_ifs <;> positivity
  have hscale : (allowance : ℝ) / Q ≤ allowance / 2 := by
    apply div_le_div_of_nonneg_left har.le (by norm_num) hQr
  have hbound := coarse_finite_threshold_simultaneous
    (coarseNodeSamplingValue k lam f value children start)
    ((allowance : ℝ) / Q) allowance Q lam hvalue (div_pos har hQpos) har
    (by field_simp) hscale hlr hlone.le bernstein
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_ofNat] at hbound
  unfold CoarseNodeDeviationEvent
  apply hbound.trans_eq
  ring

/-- The deviation event is expressed using only the root labels, yet it
implies the literal true-cost inequalities for every subtree realization. -/
theorem coarseNodeDeviationEvent_bounds {B D : ℕ} [NeZero B] {α : Type u}
    (k : ℕ) (Q lam allowance : ℚ) (f : ℝ) (hQ : Q ≠ 0)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D) (start : ℕ)
    (hevent : CoarseNodeDeviationEvent k Q lam allowance f value children start draws) :
    ∀ shift,
      (1 - (lam : ℝ)) *
          ((coarseChildrenCost k value (List.ofFn children) start shift : ℝ) /
            (f * (1 + (lam : ℝ)))) - allowance ≤
        coarseTrueThresholdSum k Q value allowance
          (fun cost => cost / (f * (1 + (lam : ℝ))))
          (List.ofFn fun i => (children i, draws i, below i)) start shift ∧
      coarseTrueThresholdSum k Q value allowance
          (fun cost => f * cost / (1 - (lam : ℝ)))
          (List.ofFn fun i => (children i, draws i, below i)) start shift ≤
        (1 + (lam : ℝ)) *
          (f * (coarseChildrenCost k value (List.ofFn children) start shift : ℝ) /
            (1 - (lam : ℝ))) + allowance := by
  intro shift
  have hlower := (abs_le.mp (hevent (shift, true))).1
  have hupper := (abs_le.mp (hevent (shift, false))).2
  simp only [coarseNodeSamplingValue, Bool.false_eq_true, ↓reduceIte] at hlower hupper
  have hlowerSum : (∑ i : Fin B,
      (coarseNodeChildCost k value children start shift i : ℝ) / (f * (1 + (lam : ℝ)))) =
      (coarseChildrenCost k value (List.ofFn children) start shift : ℝ) /
        (f * (1 + (lam : ℝ))) := by
    rw [← sum_div, coarseChildrenCost_ofFn, Nat.cast_sum]
  have hupperSum : (∑ i : Fin B,
      f * (coarseNodeChildCost k value children start shift i : ℝ) / (1 - (lam : ℝ))) =
      f * (coarseChildrenCost k value (List.ofFn children) start shift : ℝ) /
        (1 - (lam : ℝ)) := by
    rw [← sum_div, ← mul_sum, coarseChildrenCost_ofFn, Nat.cast_sum]
  rw [hlowerSum] at hlower
  rw [hupperSum] at hupper
  rw [coarseTrueThresholdSum_sample k Q allowance hQ,
    coarseTrueThresholdSum_sample k Q allowance hQ]
  constructor <;> linarith

/-- Root and actual descendant events suffice for the complete-tree
accuracy event; no approximate child value occurs in the root event. -/
theorem coarseAccuracyEvent_of_node {B D : ℕ} [NeZero B] {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam allowance : ℚ) (frame : List (Option α))
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D)
    (start : ℕ) (hQ : Q ≠ 0)
    (hchild : ∀ i, CoarseAccuracyEvent k Q lam frame (children i) (below i)
      (lam * coarseChildThreshold B Q allowance (draws i)) (coarseNodeChildStart children start i))
    (hnode : CoarseNodeDeviationEvent k Q lam allowance (coarseStructuralFactor lam D)
      (fun child => coarseShiftCost k frame child) children start draws) :
    CoarseAccuracyEvent k Q lam frame (.branch children) (draws, below) allowance start := by
  constructor
  · rw [coarseDescendantEvents_iff]
    intro i
    simpa only [List.getElem_ofFn, coarseDataListStart, coarseNodeChildStart,
      List.map_take, List.map_ofFn, Function.comp_def] using
      hchild ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
  · simpa only [List.map_ofFn, Function.comp_def] using
      coarseNodeDeviationEvent_bounds k Q lam allowance (coarseStructuralFactor lam D) hQ
        (fun child => coarseShiftCost k frame child) children draws below start hnode

/-- Simultaneous accuracy for the literal finite recursive estimator.
Every descendant is integrated conditional on its ancestor labels, with a
bound uniform in its resulting positive allowance. -/
theorem coarseAccuracyEvent_failure {B D : ℕ} [NeZero B] {α : Type u} [DecidableEq α]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α))
    (tree : CoarseSourceTree B α D) (allowance : ℚ) (start : ℕ)
    (hQ : 2 ≤ Q) (hlam : 0 < lam) (hlamone : lam < 1) (ha : 0 < allowance)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseDrawMeasure B D).real
      {draws | ¬ CoarseAccuracyEvent k Q lam frame tree draws allowance start} ≤
      (coarseInternalNodes B D : ℝ) *
        (4 * (2 * k + 1 : ℕ) * Real.exp (-(lam : ℝ) * Q / 12)) := by
  classical
  have hQpos : 0 < Q := by linarith
  induction tree generalizing allowance start with
  | leaf letter => simp only [CoarseAccuracyEvent, not_true_eq_false, Set.ofPred_false,
      measureReal_empty, coarseInternalNodes, Nat.cast_zero, zero_mul, le_refl]
  | @branch D children ih =>
    let μ := Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure
    let ν := Measure.pi fun _ : Fin B => coarseDrawMeasure B D
    let oneFailure := 4 * (2 * k + 1 : ℕ) * Real.exp (-(lam : ℝ) * Q / 12)
    let childFailure := (coarseInternalNodes B D : ℝ) * oneFailure
    let nodeBad : Set ((Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)) :=
      {data | ¬ CoarseNodeDeviationEvent k Q lam allowance (coarseStructuralFactor lam D)
        (fun child => coarseShiftCost k frame child) children start data.1}
    let childBad (i : Fin B) : Set ((Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)) :=
      {data | ¬ CoarseAccuracyEvent k Q lam frame (children i) (data.2 i)
        (lam * coarseChildThreshold B Q allowance (data.1 i)) (coarseNodeChildStart children start i)}
    have hsubset : {data : (Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D) |
        ¬ CoarseAccuracyEvent k Q lam frame (.branch children) data allowance start} ⊆
        nodeBad ∪ ⋃ i, childBad i := by
      intro data hdata
      by_cases hnode : data ∈ nodeBad
      · exact Or.inl hnode
      · right
        by_contra hchildren
        apply hdata
        obtain ⟨draws, below⟩ := data
        apply coarseAccuracyEvent_of_node k Q lam allowance frame children draws below start hQpos.ne'
        · intro i
          by_contra hi
          exact hchildren (Set.mem_iUnion.mpr ⟨i, hi⟩)
        · exact of_not_not hnode
    have hnodeProbability : (μ.prod ν).real nodeBad ≤ oneFailure := by
      have hnodeSet : nodeBad =
          {draws | ¬ CoarseNodeDeviationEvent k Q lam allowance (coarseStructuralFactor lam D)
            (fun child => coarseShiftCost k frame child) children start draws} ×ˢ Set.univ := by
        ext data
        simp only [nodeBad, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
      rw [hnodeSet, measureReal_prod_prod, probReal_univ, mul_one]
      exact coarseNodeDeviationEvent_probability k Q lam allowance (coarseStructuralFactor lam D)
        (fun child => coarseShiftCost k frame child) children start hQ hlam.le hlamone ha
        (lt_of_lt_of_le zero_lt_one (coarseStructuralFactor_one_le lam D hlam.le hlamone)) bernstein
    have hchildProbability (i : Fin B) : (μ.prod ν).real (childBad i) ≤ childFailure := by
      apply coarse_product_section_bound μ ν (childBad i) (Set.toFinite _).measurableSet
        childFailure (by dsimp [childFailure, oneFailure] <;> positivity)
      intro draws
      change ν.real {below | below i ∈ {childDraws |
        ¬ CoarseAccuracyEvent k Q lam frame (children i) childDraws
          (lam * coarseChildThreshold B Q allowance (draws i))
          (coarseNodeChildStart children start i)}} ≤ childFailure
      rw [coarse_child_projection_probability]
      exact ih i _ _ (mul_pos hlam (coarseChildThreshold_pos (draws i) hQpos ha))
    change (μ.prod ν).real _ ≤ _
    calc
      _ ≤ (μ.prod ν).real (nodeBad ∪ ⋃ i, childBad i) := measureReal_mono hsubset
      _ ≤ (μ.prod ν).real nodeBad + (μ.prod ν).real (⋃ i, childBad i) := measureReal_union_le _ _
      _ ≤ oneFailure + ∑ i, (μ.prod ν).real (childBad i) :=
        add_le_add hnodeProbability (measureReal_iUnion_fintype_le childBad)
      _ ≤ oneFailure + ∑ _ : Fin B, childFailure :=
        add_le_add_right (sum_le_sum (fun i _ => hchildProbability i)) _
      _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, coarseInternalNodes,
          Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        dsimp [childFailure, oneFailure]
        push_cast
        ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitial
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The executable initial integer estimate

The direct branches handle long targets and equality. The remaining branch
evaluates the concrete coarse recurrence at every dyadic guess, takes the
rational minimum, rounds up and clamps to the input length.
-/

namespace EditApproximation

open EditDistortion Finset MeasureTheory ProbabilityTheory

universe u

/-- A finite Bernoulli-inequality bound for the exact structural factor.
The paper's `lam = 1/(64H)` and `D ≤ H` satisfy these loose conditions. -/
theorem coarseStructuralFactor_le_two (lam : ℚ) (D : ℕ)
    (hlam : 0 ≤ lam) (hsmall : lam ≤ 1 / 4)
    (hdepth : 4 * (D : ℚ) * lam ≤ 1) : coarseStructuralFactor lam D ≤ 2 := by
  have hl : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hs : (lam : ℝ) ≤ 1 / 4 := by
    have hcast : (lam : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hsmall
    norm_num at hcast
    exact hcast
  have hd : 4 * (D : ℝ) * lam ≤ 1 := by exact_mod_cast hdepth
  have hden : 0 < 1 - (lam : ℝ) := by linarith
  have hdenTwo : 0 < 1 - 2 * (lam : ℝ) := by linarith
  have hbase : (1 + (lam : ℝ)) / (1 - (lam : ℝ)) ≤ 1 / (1 - 2 * (lam : ℝ)) := by
    apply (div_le_div_iff₀ hden hdenTwo).2
    nlinarith
  have hpower := pow_le_pow_left₀ (div_nonneg (by linarith) hden.le) hbase D
  rw [one_div_pow] at hpower
  have hbernoulli := one_add_mul_le_pow (a := -(2 * (lam : ℝ))) (by linarith) D
  have hlower : (1 : ℝ) / 2 ≤ (1 - 2 * (lam : ℝ)) ^ D := by
    simp only [mul_neg, ← sub_eq_add_neg] at hbernoulli
    nlinarith
  have hreciprocal : 1 / (1 - 2 * (lam : ℝ)) ^ D ≤ 2 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlower)).2
    linarith
  exact hpower.trans hreciprocal















theorem coarseEntryTree_word {α : Type u} (B D : ℕ) (x y : List α)
    (hcapacity : coarseEntryWidth x y ≤ B ^ D) :
    (coarseEntryTree B D x y).word = coarsePadTo (coarseEntryWidth x y) x := by
  apply coarseSourceTreeOfList_word_eq
  rw [coarsePadTo_length _ _ (le_max_left _ _)]
  exact hcapacity

theorem coarse_good_dyadic_guess (n d : ℕ) (hd : 0 < d) (hdn : d ≤ n) :
    ∃ i : CoarseGuessIndex n, d ≤ coarseGuess n i ∧ coarseGuess n i < 2 * d := by
  refine ⟨⟨Nat.clog 2 d, Nat.lt_succ_of_le (Nat.clog_mono_right 2 hdn)⟩, ?_⟩
  exact rejectionWord_range d hd

/-- Every dyadic candidate lies above the original edit cost on its
literal pathwise event, even when the guess is below the true distance. -/
theorem coarseInitialCandidate_lower {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (x y : List α)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B D)
    (hcapacity : coarseEntryWidth x y ≤ B ^ D)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hfactor : coarseStructuralFactor lam D ≤ 2)
    (hevent : let k := coarseGuess (coarseEntryWidth x y) i
      CoarseAccuracyEvent k Q lam
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B D x y) draws k 0) :
    (edit x y : ℚ) ≤ coarseInitialCandidate B D Q lam x y i draws := by
  let k := coarseGuess (coarseEntryWidth x y) i
  let tree := coarseEntryTree B D x y
  let target := coarsePadTo (coarseEntryWidth x y) y
  have hword := coarseEntryTree_word B D x y hcapacity
  have hlength : tree.word.length = target.length := by
    dsimp [tree, target]
    rw [hword, coarsePadTo_length _ _ (le_max_left _ _),
      coarsePadTo_length _ _ (le_max_right _ _)]
  have htrue := coarseTreeValue_edit_lower tree target k hlength
  have hpadding := (coarsePadding_distance_bounds x y).1
  rw [← hword] at hpadding
  have hcost : edit x y ≤ coarseTreeValue tree target k := hpadding.trans htrue
  have hcostReal : (edit x y : ℝ) ≤ coarseTreeValue tree target k := by exact_mod_cast hcost
  have haccuracy := (coarseThresholdEstimate_accurate k Q lam (coarseTargetFrame k target)
    tree draws k 0 hQ hlam hlamone (by positivity) hevent (coarseRootShift k)).1
  have hfpos : 0 < coarseStructuralFactor lam D :=
    lt_of_lt_of_le zero_lt_one (coarseStructuralFactor_one_le lam D hlam hlamone)
  have hdivide : (coarseTreeValue tree target k : ℝ) / 2 ≤
      coarseTreeValue tree target k / coarseStructuralFactor lam D :=
    div_le_div_of_nonneg_left (by positivity) hfpos hfactor
  have hcandidateReal : (edit x y : ℝ) ≤ (coarseInitialCandidate B D Q lam x y i draws : ℝ) := by
    simp only [coarseInitialCandidate, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast]
    change (edit x y : ℝ) ≤ 2 *
      ((coarseThresholdEstimate k Q lam (coarseTargetFrame k target) tree draws k 0
        (coarseRootShift k) : ℝ) + k)
    change (coarseTreeValue tree target k : ℝ) / coarseStructuralFactor lam D - k ≤ _ at haccuracy
    linarith
  exact_mod_cast hcandidateReal

/-- A dyadic guess in `[d,2d)` has the manuscript's coarse polynomial
distortion after actual threshold reconstruction and fresh padding. -/
theorem coarseInitialCandidate_upper {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (x y : List α)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B D)
    (hcapacity : coarseEntryWidth x y ≤ B ^ D)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hfactor : coarseStructuralFactor lam D ≤ 2)
    (hevent : let k := coarseGuess (coarseEntryWidth x y) i
      CoarseAccuracyEvent k Q lam
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B D x y) draws k 0)
    (hguess : edit (coarsePadTo (coarseEntryWidth x y) x)
        (coarsePadTo (coarseEntryWidth x y) y) ≤ coarseGuess (coarseEntryWidth x y) i)
    (hguessUpper : coarseGuess (coarseEntryWidth x y) i <
      2 * edit (coarsePadTo (coarseEntryWidth x y) x) (coarsePadTo (coarseEntryWidth x y) y)) :
    coarseInitialCandidate B D Q lam x y i draws ≤ ((25 + 16 * B * D) * edit x y : ℕ) := by
  let k := coarseGuess (coarseEntryWidth x y) i
  let tree := coarseEntryTree B D x y
  let target := coarsePadTo (coarseEntryWidth x y) y
  have hword := coarseEntryTree_word B D x y hcapacity
  have htrue := coarseTreeValue_edit_upper tree target k (by simpa only [tree, target, k, hword] using hguess)
  have hpadding := (coarsePadding_distance_bounds x y).2
  rw [← hword] at hpadding hguessUpper
  have htrueReal : (coarseTreeValue tree target k : ℝ) ≤
      (1 + 2 * (B : ℝ) * D) * edit tree.word target := by exact_mod_cast htrue
  have hpaddingReal : (edit tree.word target : ℝ) ≤ 2 * edit x y := by exact_mod_cast hpadding
  have hguessReal : (k : ℝ) < 2 * edit tree.word target := by exact_mod_cast hguessUpper
  have haccuracy := (coarseThresholdEstimate_accurate k Q lam (coarseTargetFrame k target)
    tree draws k 0 hQ hlam hlamone (by positivity) hevent (coarseRootShift k)).2
  change _ ≤ coarseStructuralFactor lam D * (coarseTreeValue tree target k : ℝ) + k at haccuracy
  have hfactorBound : coarseStructuralFactor lam D * (coarseTreeValue tree target k : ℝ) ≤
      2 * coarseTreeValue tree target k := mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hdistortion := mul_le_mul_of_nonneg_left hpaddingReal
    (show (0 : ℝ) ≤ 12 + 8 * (B : ℝ) * D by positivity)
  have hcandidateReal : (coarseInitialCandidate B D Q lam x y i draws : ℝ) ≤
      ((25 + 16 * B * D) * edit x y : ℕ) := by
    simp only [coarseInitialCandidate, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast]
    change 2 * ((coarseThresholdEstimate k Q lam (coarseTargetFrame k target)
      tree draws k 0 (coarseRootShift k) : ℝ) + k) ≤ _
    push_cast
    nlinarith [show (0 : ℝ) ≤ edit x y by positivity]
  exact_mod_cast hcandidateReal

/-- On the proved finite-tree events, the executable initial table entry
is an integer between the actual edit cost and its stated coarse factor. -/
theorem coarseInitialValue_bounds {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (N : ℕ) (x y : List α)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B D)
    (hcapacity : coarseEntryWidth x y ≤ B ^ D) (hN : coarseEntryWidth x y ≤ N)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hfactor : coarseStructuralFactor lam D ≤ 2)
    (hevent : CoarseInitialAccuracyEvent B D Q lam x y draws) :
    edit x y ≤ coarseInitialValue B D Q lam N x y draws ∧
      coarseInitialValue B D Q lam N x y draws ≤ (25 + 16 * B * D) * edit x y := by
  have hcN : edit x y ≤ N := (edit_le_max_length x y).trans hN
  by_cases hlong : 2 * x.length < y.length
  · have hlength := (cost_length_bounds (s := true) x y).2
    change y.length ≤ x.length + edit x y at hlength
    have hcost : edit x y ≤ y.length :=
      (edit_le_max_length x y).trans_eq (max_eq_right (by omega))
    simp only [coarseInitialValue, hlong, ↓reduceIte]
    have hlongUpper : y.length ≤ 2 * edit x y := by omega
    have hfactorNat : 2 ≤ 25 + 16 * B * D := by omega
    exact ⟨le_min hcN hcost, (min_le_right _ _).trans
      (hlongUpper.trans (Nat.mul_le_mul_right _ hfactorNat))⟩
  · by_cases hxy : x = y
    · subst y
      have hrefl : edit x x = 0 := cost_refl x
      simp only [coarseInitialValue, hlong, ↓reduceIte, hrefl, mul_zero, le_refl, and_self]
    · let d := edit (coarsePadTo (coarseEntryWidth x y) x) (coarsePadTo (coarseEntryWidth x y) y)
      have hc : 0 < edit x y := Nat.pos_of_ne_zero
        (fun hz => hxy ((cost_eq_zero_iff (s := true)).mp hz))
      have hpadding := (coarsePadding_distance_bounds x y).1
      have hd : 0 < d := lt_of_lt_of_le hc hpadding
      have hdn : d ≤ coarseEntryWidth x y := by
        have h := edit_le_max_length (coarsePadTo (coarseEntryWidth x y) x)
          (coarsePadTo (coarseEntryWidth x y) y)
        rw [coarsePadTo_length _ _ (le_max_left _ _),
          coarsePadTo_length _ _ (le_max_right _ _), max_self] at h
        exact h
      obtain ⟨i, hi, hiUpper⟩ := coarse_good_dyadic_guess (coarseEntryWidth x y) d hd hdn
      have hminimumLower : (edit x y : ℚ) ≤ coarseInitialMinimum B D Q lam x y draws := by
        unfold coarseInitialMinimum
        apply le_inf'
        intro j hj
        exact coarseInitialCandidate_lower B D Q lam x y j (draws j) hcapacity
          hQ hlam hlamone hfactor (hevent j)
      have hminimumUpper : coarseInitialMinimum B D Q lam x y draws ≤
          ((25 + 16 * B * D) * edit x y : ℕ) := by
        unfold coarseInitialMinimum
        exact (inf'_le (fun j => coarseInitialCandidate B D Q lam x y j (draws j)) (mem_univ i)).trans
          (coarseInitialCandidate_upper B D Q lam x y i (draws i) hcapacity
            hQ hlam hlamone hfactor (hevent i) hi hiUpper)
      have hceilLower : edit x y ≤ ⌈coarseInitialMinimum B D Q lam x y draws⌉₊ := by
        exact_mod_cast hminimumLower.trans (Nat.le_ceil _)
      have hceilUpper : ⌈coarseInitialMinimum B D Q lam x y draws⌉₊ ≤
          (25 + 16 * B * D) * edit x y := Nat.ceil_le.mpr hminimumUpper
      simp only [coarseInitialValue, hlong, hxy, ↓reduceIte]
      exact ⟨le_min hcN hceilLower, (min_le_right _ _).trans hceilUpper⟩

/-- The dyadic seed event has an explicit finite failure bound under
the scalar Bernstein hypothesis. -/
theorem coarseInitialAccuracyEvent_failure {B D : ℕ} [NeZero B] {α : Type u} [DecidableEq α]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (Q lam : ℚ) (x y : List α)
    (hQ : 2 ≤ Q) (hlam : 0 < lam) (hlamone : lam < 1)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseInitialMeasure B D (coarseEntryWidth x y)).real
      {draws | ¬ CoarseInitialAccuracyEvent B D Q lam x y draws} ≤
      (Nat.clog 2 (coarseEntryWidth x y) + 1 : ℕ) * (coarseInternalNodes B D : ℝ) *
        (4 * (2 * 2 ^ Nat.clog 2 (coarseEntryWidth x y) + 1 : ℕ) *
          Real.exp (-(lam : ℝ) * Q / 12)) := by
  classical
  let n := coarseEntryWidth x y
  let μ := coarseInitialMeasure B D n
  let bad (i : CoarseGuessIndex n) : Set (CoarseThresholdDraws B D) :=
    {draws | ¬ CoarseAccuracyEvent (coarseGuess n i) Q lam
      (coarseTargetFrame (coarseGuess n i) (coarsePadTo n y))
      (coarseEntryTree B D x y) draws (coarseGuess n i) 0}
  have hsubset : {draws | ¬ CoarseInitialAccuracyEvent B D Q lam x y draws} ⊆
      ⋃ i, {draws | draws i ∈ bad i} := by
    intro draws hdraws
    obtain ⟨i, hi⟩ := not_forall.mp hdraws
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hprojection (i : CoarseGuessIndex n) :
      μ.real {draws | draws i ∈ bad i} = (coarseDrawMeasure B D).real (bad i) := by
    have hmap := (measurePreserving_eval (μ := fun _ : CoarseGuessIndex n => coarseDrawMeasure B D) i).map_eq
    have hpreimage := Measure.map_apply (μ := Measure.pi fun _ : CoarseGuessIndex n => coarseDrawMeasure B D)
      (measurable_pi_apply i) (Set.toFinite (bad i)).measurableSet
    rw [hmap] at hpreimage
    exact congrArg ENNReal.toReal hpreimage.symm
  have hpoint (i : CoarseGuessIndex n) : μ.real {draws | draws i ∈ bad i} ≤
      (coarseInternalNodes B D : ℝ) *
        (4 * (2 * 2 ^ Nat.clog 2 n + 1 : ℕ) * Real.exp (-(lam : ℝ) * Q / 12)) := by
    rw [hprojection]
    have hfailure := coarseAccuracyEvent_failure (coarseGuess n i) Q lam
      (coarseTargetFrame (coarseGuess n i) (coarsePadTo n y))
      (coarseEntryTree B D x y) (coarseGuess n i) 0 hQ hlam hlamone (by dsimp [coarseGuess] <;> positivity)
      bernstein
    have hk : coarseGuess n i ≤ 2 ^ Nat.clog 2 n :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by exact Nat.le_of_lt_succ i.isLt)
    apply hfailure.trans
    gcongr
  calc
    _ ≤ μ.real (⋃ i, {draws | draws i ∈ bad i}) := measureReal_mono hsubset
    _ ≤ ∑ i, μ.real {draws | draws i ∈ bad i} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : CoarseGuessIndex n, (coarseInternalNodes B D : ℝ) *
        (4 * (2 * 2 ^ Nat.clog 2 n + 1 : ℕ) * Real.exp (-(lam : ℝ) * Q / 12)) :=
      sum_le_sum (fun i _ => hpoint i)
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, CoarseGuessIndex, Fintype.card_fin]
      dsimp [n]
      ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Computed numerical premises of the initial seed

The literal dyadic estimator uses the input-computed branching factor,
threshold and precision. Its depth and distortion bounds follow from
those integer parameters.
-/

namespace EditApproximation





theorem computed_coarse_branching (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    4 ≤ inputHeight N ∧ inputHeight N ≤ (integerParameters N).B := by
  have hlogs := inputSmallLog_bounds N hN
  have hexp : 2 ≤ heightExponent N := by omega
  have hH : 4 ≤ inputHeight N := by
    change 2 ^ 2 ≤ 2 ^ heightExponent N
    exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hexp
  have hlog : 1 ^ 4 ≤ Nat.log 2 (inputSmallLog N) := by
    apply Nat.le_log_of_pow_le (by decide : 1 < 2)
    norm_num
    omega
  have hp := coarseExponent_maximal (inputSmallLog N) 1 hlog
  have hB : inputHeight N ≤ inputHeight N ^ coarseExponent (inputSmallLog N) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ inputHeight N) hp
  exact ⟨hH, hB⟩

theorem computed_coarse_depth (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    n ≤ (integerParameters N).B ^ computedCoarseDepth N n ∧
      computedCoarseDepth N n ≤ inputHeight N := by
  have hB := computed_coarse_branching N hN hell
  have hBtwo : 2 ≤ (integerParameters N).B := by omega
  constructor
  · exact (le_max_right 1 n).trans (Nat.le_pow_clog hBtwo (max 1 n))
  · have hanti := Nat.clog_anti_left (by decide : 1 < 2) hBtwo (n := max 1 n)
    have hlength : max 1 n ≤ 2 ^ inputHeight N := by
      apply max_le Nat.one_le_two_pow
      exact hn.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
    exact hanti.trans ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hlength)

theorem computed_coarse_structuralFactor (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    coarseStructuralFactor (initialLambda N) (computedCoarseDepth N n) ≤ 2 := by
  have hH := (computed_coarse_branching N hN hell).1
  have hHQ : (4 : ℚ) ≤ inputHeight N := by exact_mod_cast hH
  have hD : (computedCoarseDepth N n : ℚ) ≤ inputHeight N := by
    exact_mod_cast (computed_coarse_depth N n hN hn hell).2
  apply coarseStructuralFactor_le_two
  · unfold initialLambda
    positivity
  · unfold initialLambda
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 64 * inputHeight N)).2
    nlinarith
  · unfold initialLambda
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 64 * inputHeight N)).2
    nlinarith

theorem computed_coarse_distortion (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    25 + 16 * (integerParameters N).B * computedCoarseDepth N n ≤
      (integerParameters N).initialFactor := by
  let H := inputHeight N
  let B := (integerParameters N).B
  have hH : 4 ≤ H := (computed_coarse_branching N hN hell).1
  have hB : 1 ≤ B := by have h := (computed_coarse_branching N hN hell).2; omega
  have hD : computedCoarseDepth N n ≤ H := (computed_coarse_depth N n hN hn hell).2
  have hpoly : 25 + 16 * H ≤ H ^ 4 := by
    have hsq : 16 ≤ H ^ 2 := by nlinarith
    have hmul := Nat.mul_le_mul_left (H ^ 2) hsq
    nlinarith
  have hscaled := Nat.mul_le_mul_left B hpoly
  have hdepth := Nat.mul_le_mul_left (16 * B) hD
  have hfactor : (integerParameters N).initialFactor = B * H ^ 4 := by
    exact pow_add H (coarseExponent (inputSmallLog N)) 4
  rw [hfactor]
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedSeed
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial-seed bounds with computed numerical parameters. -/

namespace EditApproximation

open EditDistortion

theorem computed_initialSeed_bounds {α : Type*} [DecidableEq α]
    (N B D : ℕ) (x y : List α)
    (hB : B = (integerParameters N).B)
    (hD : D = computedCoarseDepth N (coarseEntryWidth x y))
    (hN : 0 < N) (hwidth : coarseEntryWidth x y ≤ N)
    (hell : 200 ≤ inputSmallLog N)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B D)
    (hevent : CoarseInitialAccuracyEvent B D (initialThresholdQ N) (initialLambda N) x y draws) :
    edit x y ≤ coarseInitialValue B D (initialThresholdQ N) (initialLambda N) N x y draws ∧
      coarseInitialValue B D (initialThresholdQ N) (initialLambda N) N x y draws ≤
        (integerParameters N).initialFactor * edit x y := by
  have hH : (4 : ℚ) ≤ inputHeight N := by
    exact_mod_cast (computed_coarse_branching N hN hell).1
  have hden : (0 : ℚ) < 64 * (inputHeight N : ℚ) := by linarith
  have hlambda : initialLambda N < 1 := by
    unfold initialLambda
    exact (div_lt_one hden).2 (by linarith)
  have hcapacity : coarseEntryWidth x y ≤ B ^ D := by
    rw [hB, hD]
    exact (computed_coarse_depth N _ hN hwidth hell).1
  have hfactor : coarseStructuralFactor (initialLambda N) D ≤ 2 := by
    rw [hD]
    exact computed_coarse_structuralFactor N _ hN hwidth hell
  have hdistortion : 25 + 16 * B * D ≤ (integerParameters N).initialFactor := by
    rw [hB, hD]
    exact computed_coarse_distortion N _ hN hwidth hell
  have hbounds := coarseInitialValue_bounds B D (initialThresholdQ N) (initialLambda N)
    N x y draws hcapacity hwidth (pow_nonneg (Nat.cast_nonneg _) 4)
    (div_nonneg zero_le_one hden.le) hlambda hfactor hevent
  exact ⟨hbounds.1, hbounds.2.trans (Nat.mul_le_mul_right _ hdistortion)⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGlobalSeed
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Simultaneous seed failure with the computed parameters

The count includes every dyadic guess, complete coarse-tree node and shift.
Independent finite entry streams realize the actual full table law.
Symbolic recursion indices carry exact equalities to the computed parameters.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem twice_square_le_two_pow (r : ℕ) (hr : 8 ≤ r) : 2 * r ^ 2 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    rw [pow_succ 2 r]
    nlinarith

theorem computed_coarse_B_upper (N : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    (integerParameters N).B ≤ 2 ^ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hr : 8 ≤ heightExponent N := by omega
  have hp : coarseExponent (inputSmallLog N) ≤ 2 * heightExponent N := by
    have hsqrt := (Nat.sqrt_le_self (Nat.sqrt (Nat.log 2 (inputSmallLog N)))).trans
      (Nat.sqrt_le_self (Nat.log 2 (inputSmallLog N)))
    exact hsqrt.trans ((Nat.log_le_self _ _).trans (by omega))
  have hpoly := twice_square_le_two_pow (heightExponent N) hr
  have hexponent : heightExponent N * coarseExponent (inputSmallLog N) ≤ inputHeight N := by
    have hmul := Nat.mul_le_mul_left (heightExponent N) hp
    change _ ≤ 2 ^ heightExponent N
    nlinarith
  change (2 ^ heightExponent N) ^ coarseExponent (inputSmallLog N) ≤ 2 ^ inputHeight N
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hexponent

theorem computed_coarse_height_large (N : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    256 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hr : 8 ≤ heightExponent N := by omega
  change 2 ^ 8 ≤ 2 ^ heightExponent N
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hr

theorem coarseInternalNodes_add_one_le_pow (B D : ℕ) (hB : 2 ≤ B) :
    coarseInternalNodes B D + 1 ≤ B ^ D := by
  induction D with
  | zero => simp only [coarseInternalNodes, zero_add, pow_zero, le_refl]
  | succ D ih =>
    have hmul := Nat.mul_le_mul_left B ih
    simp only [coarseInternalNodes, pow_succ]
    nlinarith

theorem computed_coarseEntryTailCount (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    coarseEntryTailCount (integerParameters N).B (computedCoarseDepth N n) n ≤
      2 ^ (4 * inputHeight N + 4) := by
  let H := inputHeight N
  let B := (integerParameters N).B
  have hBtwo : 2 ≤ B := by
    have hbranch := computed_coarse_branching N hN hell
    dsimp [B]
    omega
  have hBupper : B ≤ 2 ^ H := computed_coarse_B_upper N hN hell
  have hnmax : max 1 n ≤ 2 ^ H := by
    apply max_le Nat.one_le_two_pow
    exact hn.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hnupper : n ≤ 2 ^ H := (le_max_right 1 n).trans hnmax
  have hlog : Nat.clog 2 n ≤ H := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hnupper
  have hguesses : Nat.clog 2 n + 1 ≤ 2 ^ H := by
    have hself := Nat.lt_pow_self (by decide : 1 < 2) (n := H)
    omega
  have hnodes : coarseInternalNodes B (computedCoarseDepth N n) ≤ 2 ^ (2 * H) := by
    have hcount := coarseInternalNodes_add_one_le_pow B (computedCoarseDepth N n) hBtwo
    have hpower := intervalTreeDepth_power_le B n hBtwo
    have hproduct : B * max 1 n ≤ 2 ^ H * 2 ^ H := Nat.mul_le_mul hBupper hnmax
    rw [← pow_add] at hproduct
    change B ^ computedCoarseDepth N n ≤ B * max 1 n at hpower
    have hsum : H + H = 2 * H := by omega
    rw [hsum] at hproduct
    omega
  have hguessPower : 2 ^ Nat.clog 2 n ≤ 2 ^ H := Nat.pow_le_pow_right (by decide : 0 < 2) hlog
  have hshift : 4 * (2 * 2 ^ Nat.clog 2 n + 1) ≤ 2 ^ (H + 4) := by
    have hone := Nat.one_le_two_pow (n := H)
    rw [pow_add]
    norm_num only [show (2 : ℕ) ^ 4 = 16 by norm_num]
    nlinarith
  have hproduct := Nat.mul_le_mul (Nat.mul_le_mul hguesses hnodes) hshift
  apply hproduct.trans_eq
  rw [← pow_add, ← pow_add]
  congr 1
  omega

theorem computed_coarse_tail_exponent (N : ℕ) :
    -(initialLambda N : ℝ) * initialThresholdQ N / 12 = -(inputHeight N : ℝ) ^ 3 / 768 := by
  have hH : (inputHeight N : ℝ) ≠ 0 := by
    have hpos : 0 < inputHeight N := by unfold inputHeight; positivity
    exact_mod_cast hpos.ne'
  simp only [initialLambda, initialThresholdQ, Rat.cast_div, Rat.cast_mul,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow]
  field_simp [hH]
  ring

theorem coarse_global_exponential_failure (H : ℕ) (hH : 256 ≤ H) :
    (2 : ℝ) ^ (10 * H) * Real.exp (-(H : ℝ) ^ 3 / 768) < 1 / 100 := by
  have hHr : (256 : ℝ) ≤ H := by exact_mod_cast hH
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo (10 * H)
  rw [← Real.exp_nat_mul, mul_one] at hpower
  have hexponent : (10 * H : ℕ) - (H : ℝ) ^ 3 / 768 ≤ -7 := by
    have hsq : (65536 : ℝ) ≤ (H : ℝ) ^ 2 := by nlinarith
    have hcube := mul_le_mul_of_nonneg_right hsq (show (0 : ℝ) ≤ H by positivity)
    push_cast
    nlinarith
  have hseven : (128 : ℝ) ≤ Real.exp 7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 7
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one,
      show (2 : ℝ) ^ 7 = 128 by norm_num] using h
  have hnegative : Real.exp (-7) ≤ (1 : ℝ) / 128 := by
    rw [Real.exp_neg, ← one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hseven
  calc
    _ ≤ Real.exp (10 * H : ℕ) * Real.exp (-(H : ℝ) ^ 3 / 768) :=
      mul_le_mul_of_nonneg_right hpower (Real.exp_nonneg _)
    _ = Real.exp ((10 * H : ℕ) - (H : ℝ) ^ 3 / 768) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-7) := Real.exp_le_exp.mpr hexponent
    _ ≤ 1 / 128 := hnegative
    _ < 1 / 100 := by norm_num

/-- Symbolic recursion indices prevent irrelevant normalization of integer
logarithms in dependent draw types. The equalities retain the exact computed
algorithm, rather than replacing it with a larger or assumed seed contract. -/
theorem computed_initialAccuracy_failure (N B D : ℕ)
    [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (hB : B = (integerParameters N).B)
    {α : Type*} [DecidableEq α] (x y : List α)
    (hD : D = computedCoarseDepth N (coarseEntryWidth x y))
    (hN : 0 < N) (hwidth : coarseEntryWidth x y ≤ N)
    (hell : 200 ≤ inputSmallLog N)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseInitialMeasure B D (coarseEntryWidth x y)).real
      {draws | ¬ CoarseInitialAccuracyEvent B D (initialThresholdQ N) (initialLambda N) x y draws} ≤
      (2 : ℝ) ^ (4 * inputHeight N + 4) * Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) := by
  have hH : (256 : ℚ) ≤ inputHeight N := by exact_mod_cast computed_coarse_height_large N hN hell
  have hQ : (2 : ℚ) ≤ initialThresholdQ N := by
    unfold initialThresholdQ
    exact (by norm_num : (2 : ℚ) ≤ 256 ^ 4).trans
      (pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 256) hH 4)
  have hden : (0 : ℚ) < 64 * inputHeight N :=
    mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 256) hH)
  have hlam : (0 : ℚ) < initialLambda N := by
    unfold initialLambda
    exact div_pos (by norm_num) hden
  have hlamone : initialLambda N < 1 := by
    unfold initialLambda
    apply (div_lt_one hden).2
    linarith only [hH]
  have hfailure := coarseInitialAccuracyEvent_failure (B := B) (D := D)
    (initialThresholdQ N) (initialLambda N) x y hQ hlam hlamone bernstein
  rw [computed_coarse_tail_exponent] at hfailure
  have hcount : coarseEntryTailCount B D (coarseEntryWidth x y) ≤
      2 ^ (4 * inputHeight N + 4) := by
    rw [hB, hD]
    exact computed_coarseEntryTailCount N (coarseEntryWidth x y) hN hwidth hell
  have hcountReal : (coarseEntryTailCount B D (coarseEntryWidth x y) : ℝ) ≤
      (2 : ℝ) ^ (4 * inputHeight N + 4) := by exact_mod_cast hcount
  have hfailureCount : (coarseInitialMeasure B D (coarseEntryWidth x y)).real
      {draws | ¬ CoarseInitialAccuracyEvent B D
        (initialThresholdQ N) (initialLambda N) x y draws} ≤
      (coarseEntryTailCount B D (coarseEntryWidth x y) : ℝ) *
        Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) := by
    convert hfailure using 1
    all_goals try with_reducible_and_instances rfl
    simp only [coarseEntryTailCount, Nat.cast_mul, Nat.cast_ofNat]
    ring
  exact hfailureCount.trans (mul_le_mul_of_nonneg_right hcountReal (Real.exp_nonneg _))





/-- The full finite table law fails with probability below one percent.
The cardinal bound is supplied by the actual labeled state-domain count. -/
theorem computed_fullSeed_failure (N B : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    {I α : Type*} [Fintype I] [DecidableEq α] (depth : I → ℕ)
    (x y : I → List α) (hB : B = (integerParameters N).B)
    (hD : ∀ i, depth i = computedCoarseDepth N (coarseEntryWidth (x i) (y i)))
    (hN : 0 < N) (hwidth : ∀ i, coarseEntryWidth (x i) (y i) ≤ N)
    (hcount : Fintype.card I ≤ 2 ^ (5 * inputHeight N))
    (hell : 200 ≤ inputSmallLog N)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseFullSeedMeasure B depth x y).real
      {draws | ¬ CoarseFullSeedAccuracyEvent N B depth x y draws} < 1 / 100 := by
  classical
  let μ := coarseFullSeedMeasure B depth x y
  let ν (i : I) := coarseInitialMeasure B (depth i) (coarseEntryWidth (x i) (y i))
  let bad (i : I) : Set (CoarseGuessIndex (coarseEntryWidth (x i) (y i)) →
      CoarseThresholdDraws B (depth i)) :=
    {draws | ¬ CoarseInitialAccuracyEvent B (depth i)
      (initialThresholdQ N) (initialLambda N) (x i) (y i) draws}
  have hsubset : {draws | ¬ CoarseFullSeedAccuracyEvent N B depth x y draws} ⊆
      ⋃ i, {draws | draws i ∈ bad i} := by
    intro draws hdraws
    obtain ⟨i, hi⟩ := not_forall.mp hdraws
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hprojection (i : I) : μ.real {draws | draws i ∈ bad i} = (ν i).real (bad i) := by
    have hmap := (measurePreserving_eval (μ := ν) i).map_eq
    have hpreimage := Measure.map_apply (μ := Measure.pi ν) (measurable_pi_apply i)
      (Set.toFinite (bad i)).measurableSet
    rw [hmap] at hpreimage
    exact congrArg ENNReal.toReal hpreimage.symm
  have hpoint (i : I) : μ.real {draws | draws i ∈ bad i} ≤
      (2 : ℝ) ^ (4 * inputHeight N + 4) * Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) := by
    rw [hprojection]
    exact computed_initialAccuracy_failure N B (depth i) hB (x i) (y i) (hD i)
      hN (hwidth i) hell bernstein
  have hH : 256 ≤ inputHeight N := computed_coarse_height_large N hN hell
  have htotal : Fintype.card I * 2 ^ (4 * inputHeight N + 4) ≤ 2 ^ (10 * inputHeight N) := by
    calc
      _ ≤ 2 ^ (5 * inputHeight N) * 2 ^ (4 * inputHeight N + 4) := Nat.mul_le_mul_right _ hcount
      _ = 2 ^ (9 * inputHeight N + 4) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have htotalReal : (Fintype.card I : ℝ) * (2 : ℝ) ^ (4 * inputHeight N + 4) ≤
      (2 : ℝ) ^ (10 * inputHeight N) := by exact_mod_cast htotal
  calc
    _ ≤ μ.real (⋃ i, {draws | draws i ∈ bad i}) := measureReal_mono hsubset
    _ ≤ ∑ i, μ.real {draws | draws i ∈ bad i} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : I, (2 : ℝ) ^ (4 * inputHeight N + 4) * Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) :=
      sum_le_sum (fun i _ => hpoint i)
    _ = ((Fintype.card I : ℝ) * (2 : ℝ) ^ (4 * inputHeight N + 4)) *
        Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) := by simp only [sum_const, card_univ, nsmul_eq_mul, mul_assoc]
    _ ≤ (2 : ℝ) ^ (10 * inputHeight N) * Real.exp (-(inputHeight N : ℝ) ^ 3 / 768) :=
      mul_le_mul_of_nonneg_right htotalReal (Real.exp_nonneg _)
    _ < 1 / 100 := coarse_global_exponential_failure _ hH

/-- The executable full integer table uses exactly the supplied recursion
indices. Computed-parameter equalities appear only in its correctness proofs. -/


theorem computed_fullSeedTable_pathwise (N B : ℕ) {I α : Type*} [DecidableEq α]
    (depth : I → ℕ) (x y : I → List α) (hB : B = (integerParameters N).B)
    (hD : ∀ i, depth i = computedCoarseDepth N (coarseEntryWidth (x i) (y i)))
    (hN : 0 < N) (hwidth : ∀ i, coarseEntryWidth (x i) (y i) ≤ N)
    (hell : 200 ≤ inputSmallLog N) (draws : CoarseFullSeedDraws B depth x y)
    (hevent : CoarseFullSeedAccuracyEvent N B depth x y draws) :
    ∀ i, EditDistortion.edit (x i) (y i) ≤ coarseFullSeedTable N B depth x y draws i ∧
      coarseFullSeedTable N B depth x y draws i ≤
        (integerParameters N).initialFactor * EditDistortion.edit (x i) (y i) := by
  intro i
  exact computed_initialSeed_bounds N B (depth i) (x i) (y i) hB (hD i)
    hN (hwidth i) hell (draws i) (hevent i)

/-- Simultaneous finite table accuracy under the scalar Bernstein hypothesis. -/
theorem computed_fullSeedTable_accuracy (N B : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    {I α : Type*} [Fintype I] [DecidableEq α] (depth : I → ℕ) (x y : I → List α)
    (hB : B = (integerParameters N).B)
    (hD : ∀ i, depth i = computedCoarseDepth N (coarseEntryWidth (x i) (y i)))
    (hN : 0 < N) (hwidth : ∀ i, coarseEntryWidth (x i) (y i) ≤ N)
    (hcount : Fintype.card I ≤ 2 ^ (5 * inputHeight N))
    (hell : 200 ≤ inputSmallLog N)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseFullSeedMeasure B depth x y).real {draws | ¬ ∀ i,
      EditDistortion.edit (x i) (y i) ≤ coarseFullSeedTable N B depth x y draws i ∧
      coarseFullSeedTable N B depth x y draws i ≤
        (integerParameters N).initialFactor * EditDistortion.edit (x i) (y i)} < 1 / 100 := by
  have hsubset : {draws | ¬ ∀ i,
      EditDistortion.edit (x i) (y i) ≤ coarseFullSeedTable N B depth x y draws i ∧
      coarseFullSeedTable N B depth x y draws i ≤
        (integerParameters N).initialFactor * EditDistortion.edit (x i) (y i)} ⊆
      {draws | ¬ CoarseFullSeedAccuracyEvent N B depth x y draws} := by
    intro draws hdraws hevent
    exact hdraws (computed_fullSeedTable_pathwise N B depth x y hB hD hN hwidth hell draws hevent)
  exact (measureReal_mono hsubset).trans_lt
    (computed_fullSeed_failure N B depth x y hB hD hN hwidth hcount hell bernstein)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_StateDomain
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual finite labeled state type

Physical nodes are retained as depth/path pairs. In particular, repeated
empty intervals remain distinct entries of the seed and refinement tables.
-/

namespace EditApproximation

open Finset





theorem targetInterval_card_le (n : ℕ) :
    Fintype.card (TargetInterval n) ≤ (targetStates n).length := by
  exact (targetStates n).toFinset_card_le





theorem physicalNode_card (M J : ℕ) :
    Fintype.card (PhysicalNode M J) =
      ∑ d ∈ range (J + 1), Fintype.card (TreeLayer M d) := by
  rw [Fintype.card_sigma]
  rw [sum_fin_eq_sum_range]
  apply sum_congr rfl
  intro d hd
  rw [dite_eq_left (mem_range.mp hd)]

theorem labeledEntry_card_le (M nx ny : ℕ) :
    Fintype.card (LabeledEntry M nx ny) ≤ labeledStateCount M nx ny := by
  rw [Fintype.card_prod, physicalNode_card]
  exact Nat.mul_le_mul_left _ (targetInterval_card_le ny)

theorem computed_labeledEntry_card_le (N nx ny : ℕ) (hN : 0 < N)
    (hnx : nx ≤ N) (hny : ny ≤ N) (hell : 200 ≤ inputSmallLog N) :
    Fintype.card (LabeledEntry (integerParameters N).M nx ny) ≤ 2 ^ (5 * inputHeight N) :=
  (labeledEntry_card_le _ _ _).trans (computed_labeledStateCount_le N nx ny hN hnx hny hell)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCoarseSeedLaw
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The clamped incoming seed table is the image of the actual complete
coarse sampler. Its simultaneous initial accuracy is a derived fact. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section CoarseLaw

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (N B : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)





variable [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]

theorem physicalCoarseSeedLaw_failure (hN : 0 < N)
    (hsize : source.length + target.length ≤ N) (hell : 200 ≤ inputSmallLog N)
    (hB : B = (integerParameters N).B) (hM : M = (integerParameters N).M)
    (hJ : J = intervalTreeDepth M source.length)
    (hdepth : ∀ state, depth state = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source state.1) (substring target state.2.lo state.2.hi)))
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (physicalCoarseSeedLaw source target N B depth).real
      {seed | ¬ physicalSeedGood source target ((integerParameters N).initialFactor : ℚ) seed} < 1 / 100 := by
  classical
  have hwidth (state : PhysicalEntry M J target.length) :
      coarseEntryWidth (physicalSource source state.1) (substring target state.2.lo state.2.hi) ≤ N := by
    apply max_le
    · exact (physicalSource_length_le source state.1).trans (by omega)
    · have hlen : (substring target state.2.lo state.2.hi).length ≤ target.length := by
        simp only [substring, List.length_drop, List.length_take]
        exact (Nat.sub_le _ _).trans (min_le_right _ _)
      exact hlen.trans (by omega)
  have hcount : Fintype.card (PhysicalEntry M J target.length) ≤ 2 ^ (5 * inputHeight N) := by
    rw [hJ, hM]
    exact computed_labeledEntry_card_le N source.length target.length hN (by omega) (by omega) hell
  have h := computed_fullSeedTable_accuracy N B depth
    (fun state : PhysicalEntry M J target.length => physicalSource source state.1)
    (fun state : PhysicalEntry M J target.length => substring target state.2.lo state.2.hi)
    hB hdepth hN hwidth hcount hell bernstein
  rw [physicalCoarseSeedLaw, map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  have hevents : (physicalCoarseSeedTable source target N B depth) ⁻¹'
      {seed | ¬ physicalSeedGood source target ((integerParameters N).initialFactor : ℚ) seed} =
      {draw : PhysicalCoarseDraw source target B depth | ¬ ∀ state : PhysicalEntry M J target.length,
        stateEditCost (physicalSource source state.1) target state.2 ≤
          coarseFullSeedTable N B depth
            (fun state : PhysicalEntry M J target.length => physicalSource source state.1)
            (fun state : PhysicalEntry M J target.length => substring target state.2.lo state.2.hi) draw state ∧
        coarseFullSeedTable N B depth
            (fun state : PhysicalEntry M J target.length => physicalSource source state.1)
            (fun state : PhysicalEntry M J target.length => substring target state.2.lo state.2.hi) draw state ≤
          (integerParameters N).initialFactor * stateEditCost (physicalSource source state.1) target state.2} := by
    ext draw
    apply not_congr
    unfold physicalSeedGood clampedSeedNat physicalCoarseSeedTable
    constructor
    · intro hg state
      exact ⟨(hg state).1, by exact_mod_cast (hg state).2⟩
    · intro hg state
      exact ⟨(hg state).1, by exact_mod_cast (hg state).2⟩
  rw [hevents]
  exact h

end CoarseLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalFinalAccuracy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final fresh bounded-key local query, following the actual local
median schedule, has the required approximation probability. The incoming
law is supplied by the concrete coarse sampler in the final theorem. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Coarse

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H B : ℕ)
  [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

theorem local_physical_conditional_accuracy_oai (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
    (hsize : source.length + target.length ≤ N)
    (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
    (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
    (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
    (hB : B = (integerParameters N).B)
    (hdepth : ∀ state, depth state = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source state.1) (substring target state.2.lo state.2.hi)))
    (coarseBernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure))
    (groupBernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
      FiniteBernsteinInput (Measure.pi fun _ : Fin
        (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
        (PMF.uniformOfFintype (Fin M)).toMeasure))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (haccuracy : 10 ≤ (inputSmallLog N : ℝ) * epsilon) :
    (2 / 3 : ℝ) ≤ (localFinalProgramLaw (R := R) source target N P T S H
      (physicalCoarseSeedLaw source target N B depth)).real
      {pair | EditDistortion.edit source target ≤ localWholeFinalAnswer (R := R) source target N P T S H pair ∧
        (localWholeFinalAnswer (R := R) source target N P T S H pair : ℝ) ≤
          (1 + epsilon) * EditDistortion.edit source target} := by
  classical
  have hsmall : 256 ≤ (2 : ℕ) ^ 1000 := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
    norm_num only [show (2 : ℕ) ^ 8 = 256 by norm_num] at h
    exact h
  have hcut : 200 ≤ inputSmallLog N := by omega
  have hinitial := physicalCoarseSeedLaw_failure source target N B depth hN hsize hcut
    hB hMeq hJeq hdepth coarseBernstein
  have h := localFinalProgram_accuracy (R := R) source target N P T S H hN hell hMeq hJeq hPeq
    hTeq hSeq hHeq hsize groupBernstein (physicalCoarseSeedLaw source target N B depth)
    hinitial.le (finalTargetState target.length) epsilon hepsilon haccuracy
  apply (by norm_num : (2 / 3 : ℝ) ≤ 4 / 5).trans
  simpa only [localWholeFinalAnswer, stateEditCost, finalTargetState, substring,
    List.take_length, List.drop_zero] using h

end Coarse

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.local_physical_conditional_accuracy_oai.{u_1} := @OAI.EditApproximation.local_physical_conditional_accuracy_oai.{u_1}
