-- Prove2me | solution 1 for OAI.SourceBurnside.ConcreteSource.steinberg_infinite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T16:11:25.674502+00:00
-- url     : https://prove2.me/submissions/19eac39b-3513-431d-acdb-17dd2e854c8f

import Mathlib
import Definitions.Def_PeriodicGroup
import Definitions.Def_OAIQ18Pg012

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Palette
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.instFintypeCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Palette

variable {C : Type u} {A : Type v}

variable (head : A → Prop)

lemma prefix_passed (p : List (Cell C A)) (a : Cell C A) (x : C)
    (hc : List.IsChain (fun a b => Pair a.check b.check) (p ++ [a]))
    (ha : a.check = .passed x ∨ a.check = .head x) :
    ∀ c ∈ p, c.check = .passed x := by
  induction p with
  | nil => simp
  | cons b p ih =>
    have ht := ih hc.tail
    have hb : b.check = .passed x := by
      cases p with
      | nil =>
        have hp : Pair b.check a.check := hc.rel
        rcases ha with ha | ha <;> rw [ha] at hp
        · generalize hb : b.check = ck at hp
          cases hp
          rfl
        · generalize hb : b.check = ck at hp
          cases hp
          rfl
      | cons c t =>
        have hp : Pair b.check c.check := hc.rel
        rw [ht c (by simp)] at hp
        generalize hb : b.check = ck at hp
        cases hp
        rfl
    simpa using (show b.check = .passed x ∧ ∀ c ∈ p, c.check = .passed x from ⟨hb, ht⟩)

theorem not_zero_of_invariants {w : List (Cell C A)}
    (hsyn : Syntax w) (hsafe : Safe w) (hnd : (w.map Cell.color).Nodup)
    (hcover : ∀ x : C, x ∈ w.map Cell.color) : ¬ Zero w := by
  rintro (⟨a, ha, x, hx, hax⟩ | ⟨p, a, b, s, rfl, hab⟩ | ⟨p, a, x, rfl, hx, hax⟩)
  · exact hsafe a ha x hx hax
  · have hn : (a.color :: b.color :: s.map Cell.color).Nodup :=
      (List.nodup_append.mp (by simpa using hnd)).2.1
    exact (List.nodup_cons.mp hn).1 (by simp [hab])
  · have hp := prefix_passed p a x hsyn.1 (Or.inr hx)
    obtain ⟨b, hb, hbx⟩ := List.mem_map.mp (hcover x)
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hsafe b (List.mem_append_left _ hb) x (hp b hb) hbx
    · exact hax hbx

end SourceBurnside.Palette

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_HeadTour
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instDecidableCellCut _root_.OAI.SourceBurnside.FiniteTable.instTransCellGeomRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable
open LocalSyntax
open LocalSyntax.Skeleton

variable {q : ℕ} [NeZero q]

lemma zero_lengths (S : Schedule q) (dataSize : ℕ) (v : List (Cell q))
    (h : Zero S dataSize v) : 1≤v.length ∧ v.length≤2 := by
  rcases h with ⟨c,rfl,_⟩ | ⟨a,b,rfl,_⟩ <;> simp

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TableEncoding
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instDecidableCellCut _root_.OAI.SourceBurnside.FiniteTable.instTransCellGeomRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

lemma unary_idle_first {a b : Cell q} (h : Unary S a b) (ha : a.marker=.idle) :
    ∃ p, a.pos=.core p ∧ p.val=0 := by
  cases h <;> simp [Cell.idle,Cell.boundary,Cell.full,Cell.marker,
    Skeleton.mark] at ha
  case create c s hf => exact hf.2

lemma unary_ne_idle_right {a b : Cell q} (h : Unary S a b) : b.marker ≠ .idle := by
  cases h <;> simp [Cell.boundary,Cell.full,Cell.marker,Skeleton.mark]

lemma no_step_interior_idle {c : Cell q} (hm : c.marker=.idle)
    (hp : ∃ p, c.pos=.core p ∧ p.val ≠ 0) (w : List (Cell q)) : ¬Step S d [c] w := by
  rintro ⟨l,r,a,b,he,hw,hh⟩
  have hl := congrArg List.length he
  have hn := (replacement_lengths S d a b hh).2.1
  simp only [List.length_singleton,List.length_append] at hl
  have hll : l=[] := List.length_eq_zero_iff.mp (by omega)
  have hrr : r=[] := List.length_eq_zero_iff.mp (by omega)
  subst l; subst r
  simp only [List.nil_append,List.append_nil] at he hw
  subst a; subst w
  rcases hh.2 with ⟨a,b,he,rfl,hh⟩ | ⟨a,b,a',b',he,hw,hh⟩
  · have hca : c=a := by simpa using he
    subst a
    rcases hh with hh | hh
    · rcases unary_idle_first hh hm with ⟨p,hp',hv⟩
      rcases hp with ⟨r,hr,hn⟩
      have he : r=p := by simpa [hr] using hp'
      exact hn (he.symm ▸ hv)
    · exact unary_ne_idle_right hh hm
  · simp at he

theorem reach_interior_idle_iff {c : Cell q} (hm : c.marker=.idle)
    (hp : ∃ p, c.pos=.core p ∧ p.val ≠ 0) (w : List (Cell q)) :
    Reach S d [c] w ↔ w=[c] := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail h e ih => exact (no_step_interior_idle hm hp _ (ih ▸ e)).elim
  · rintro rfl; exact .refl

lemma idleCore_format (p : Fin q) : (idleCore p).Format S d := by
  simp [Cell.Format,idleCore,Skeleton.Admissible,Cell.isPalette,Cell.isCore,
    Cell.pos,Cell.marker,Cell.metadata,IsHead]

lemma idleCore_not_zero (p : Fin q) : ¬ UnaryZero S d (idleCore p) := by
  rintro (h | h | ⟨x,h,_⟩)
  · exact h (idleCore_format p)
  · simp [SemanticZero,idleCore,Cell.marker] at h
  · simp [idleCore,Cell.pos] at h

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q]

theorem idleCore_not_contextual_zero (S : Schedule q) (d : ℕ) (p : Fin q)
    (l z r : List (Cell q)) (hz : Zero S d z) :
    [idleCore p] ≠ l++z++r := by
  intro he
  have hl := congrArg List.length he
  have hn := (zero_lengths S d z hz).1
  simp only [List.length_singleton,List.length_append] at hl
  have hll : l=[] := List.length_eq_zero_iff.mp (by omega)
  have hrr : r=[] := List.length_eq_zero_iff.mp (by omega)
  subst l; subst r
  simp only [List.nil_append,List.append_nil] at he
  subst z
  rcases hz with ⟨c,he,hc⟩ | ⟨a,b,he,_⟩
  · have hc' : idleCore p=c := by simpa using he
    exact idleCore_not_zero p (hc'.symm ▸ hc)
  · simp at he

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Transactions
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instDecidableCellCut _root_.OAI.SourceBurnside.FiniteTable.instTransCellGeomRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

namespace Cell
omit [NeZero q] in
lemma read_palette (a : Address q) (c : Cell q) (h : c.isPalette) : c.read a = 0 := by
  obtain ⟨x,hx⟩ := h
  cases a <;> simp [read,hx]
omit [NeZero q] in
@[simp] lemma read_setColor (a : Address q) (c : Cell q) (x : Fin q) : (c.setColor x).read a = 0 := by
  apply read_palette
  exact ⟨x,rfl⟩

omit [NeZero q] in
lemma lockedReads_refl (a : Cell q) : a.LockedReads a := by intro _ _ x; rfl
end Cell

lemma Unary.lockedReads {a b : Cell q} (h : Unary S a b) : a.LockedReads b := by
  cases h <;> intro ha hb x <;> simp only [Cell.read_full,Cell.read_boundary]
  case create c s h => exact (ha rfl).elim

lemma Binary.lockedReads {a b a' b' : Cell q} (h : Binary S a b a' b') :
    a.LockedReads a' ∧ b.LockedReads b' := by
  cases h with
  | acquire a b s hp =>
    constructor
    · intro ha hb x; rfl
    · intro ha hb x; exact (ha rfl).elim
  | swap a b x y ha hb he hf hf' =>
    constructor <;> intro _ _ z
    · rw [Cell.read_palette z a ⟨x,ha⟩,Cell.read_palette z b ⟨y,hb⟩]
    · rw [Cell.read_palette z a ⟨x,ha⟩,Cell.read_palette z b ⟨y,hb⟩]
  | read_left a b s j r hp => constructor <;> intro _ _ x <;> rfl
  | read_right a b s j r hp => constructor <;> intro _ _ x <;> rfl
  | undo_left a b s j r hp => constructor <;> intro _ _ x <;> rfl
  | undo_right a b s j r hp => constructor <;> intro _ _ x <;> rfl
  | checker_create a b p x ha hp hb => constructor <;> intro _ _ x <;> rfl
  | checker_advance a b v x ha hb hv => constructor <;> intro _ _ x <;> rfl

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_ConnectedWords
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instTransCellGeomRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton

namespace Connected
variable {N : ℕ} {cut cut' : Fin N → Prop} {i j k a b : Fin N}
lemma congr (h : ∀ i, cut i ↔ cut' i) : Connected cut i j ↔ Connected cut' i j := by
  unfold Connected
  simp only [h]

lemma edit_unrelated (hab : a.val+1=b.val)
    (hc : ∀ k, k≠a → (cut k ↔ cut' k))
    (hia : ¬Connected cut i a) (hib : ¬Connected cut i b) :
    Connected cut i j ↔ Connected cut' i j := by
  have not_cross (h : Connected cut' i j) :
      ¬ (min i.val j.val ≤ a.val ∧ a.val < max i.val j.val) := by
    rintro ⟨ha,ha'⟩
    by_cases hi : i.val ≤ a.val
    · apply hia
      intro t ht ht'
      have hne : t≠a := by intro he; subst t; omega
      exact (not_congr (hc t hne)).mpr (h t (by omega) (by omega))
    · apply hib
      intro t ht ht'
      have hne : t≠a := by intro he; subst t; omega
      exact (not_congr (hc t hne)).mpr (h t (by omega) (by omega))
  constructor
  · intro h t ht ht'
    have hne : t≠a := by
      intro he; subst t
      apply hia
      exact h.subinterval (by omega) (by omega) (by omega) (by omega)
    exact (not_congr (hc t hne)).mp (h t ht ht')
  · intro h t ht ht'
    have hne : t≠a := by intro he; subst t; exact not_cross h ⟨ht,ht'⟩
    exact (not_congr (hc t hne)).mpr (h t ht ht')
end Connected

variable {q N : ℕ}

variable [NeZero q]

lemma Unary.cut_iff {S : Schedule q} {a b : Cell q} (he : Unary S a b) :
    a.skeleton.rightExternal ↔ b.skeleton.rightExternal := by
  cases he <;>
    simp only [Cell.idle,Cell.boundary,Cell.full,Skeleton.rightExternal,
      Skeleton.mark_marker,Skeleton.mark_last] <;> simp_all

namespace UnaryAt
variable {S : Schedule q} {f g : Fin N → Cell q} {i : Fin N} (hu : UnaryAt S f g i)
include hu
lemma cuts : ∀ h, cellCut f h ↔ cellCut g h := by
  intro h
  by_cases he : h=i
  · subst h; exact hu.edge.cut_iff
  · simp only [cellCut,hu.off h he]
lemma reads : ∀ h, (f h).LockedReads (g h) := by
  intro h
  by_cases he : h=i
  · subst h; exact hu.edge.lockedReads
  · rw [hu.off h he]; exact Cell.lockedReads_refl _
end UnaryAt

namespace BinaryAt
variable {S : Schedule q} {f g : Fin N → Cell q} {i j : Fin N} (hb : BinaryAt S f g i j)
include hb
lemma reads : ∀ h, (f h).LockedReads (g h) := by
  intro h
  by_cases he : h=i
  · subst h; exact hb.edge.lockedReads.1
  · by_cases he' : h=j
    · subst h; exact hb.edge.lockedReads.2
    · rw [hb.off h he he']; exact Cell.lockedReads_refl _
lemma cuts (hi : cellCut f i ↔ cellCut g i) (hj : cellCut f j ↔ cellCut g j) :
    ∀ h, cellCut f h ↔ cellCut g h := by
  intro h
  by_cases he : h=i
  · subst h; exact hi
  · by_cases he' : h=j
    · subst h; exact hj
    · simp only [cellCut,hb.off h he he']
lemma cuts_off (hj : cellCut f j ↔ cellCut g j) :
    ∀ h, h≠i → (cellCut f h ↔ cellCut g h) := by
  intro h hi
  by_cases he : h=j
  · subst h; exact hj
  · simp only [cellCut,hb.off h hi he]
end BinaryAt

namespace Verification
open scoped BigOperators
variable (S : Schedule q)

omit [NeZero q] in
lemma sum_succ (f : Fin N → Cell q) (h : Fin N) (j : Fin q) (a : Fin N) :
    sum S f h j (a.val+1)=sum S f h j a.val+
      if SameRegion f h a then (f a).delta (S.clause (f h).metadata.task j) else 0 := by
  classical
  have here : ∀ i : Fin N,
      (if SameRegion f h i ∧ i.val < a.val+1 then (f i).delta (S.clause (f h).metadata.task j) else 0) =
      (if SameRegion f h i ∧ i.val < a.val then (f i).delta (S.clause (f h).metadata.task j) else 0)+
      (if i=a then (if SameRegion f h a then (f a).delta (S.clause (f h).metadata.task j) else 0) else 0) := by
    intro i
    by_cases hic : SameRegion f h i
    · by_cases hi : i.val < a.val
      · have hne : i≠a := by intro he; subst i; omega
        simp [hic,hi,show i.val < a.val+1 by omega,hne]
      · by_cases he : i=a
        · subst i; simp [hic]
        · have hn : ¬ i.val < a.val+1 := by have := Fin.val_ne_of_ne he; omega
          simp [hic,hi,hn,he]
    · by_cases he : i=a
      · subst i; simp [hic]
      · simp [hic,he]
  simp only [sum,here,Finset.sum_add_distrib]
  simp

omit [NeZero q] in
lemma sum_congr {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {h k : Fin N} (hh : (f h).skeleton.IsHead) (hk : (g k).skeleton.IsHead)
    (hc : ∀ i, SameRegion f h i ↔ SameRegion g k i)
    (ht : (f h).metadata.task=(g k).metadata.task)
    (hr : ∀ i, (f i).LockedReads (g i)) (j : Fin q) (t : ℕ) :
    sum S f h j t=sum S g k j t := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : SameRegion f h i ∧ i.val < t
  · rw [ite_eq_left hm,ite_eq_left ⟨(hc i).mp hm.1,hm.2⟩]
    unfold Cell.delta
    rw [ht]
    funext r
    exact hr i (hf.region_locked hh hm.1.symm)
      (hg.region_locked hk ((hc i).mp hm.1).symm) _
  · have hm' : ¬(SameRegion g k i ∧ i.val < t) := by simpa only [←hc i] using hm
    rw [ite_eq_right hm,ite_eq_right hm']

omit [NeZero q] in
lemma leftSum_first {f : Fin N → Cell q} (hf : Coherent f) (h : Fin N) (j : Fin q)
    (he : (f h).skeleton.leftExternal) : leftSum S f h j=0 := by
  classical
  unfold leftSum sum
  apply Finset.sum_eq_zero
  intro i hi
  have hm : ¬(SameRegion f h i ∧ i.val < h.val) := by
    rintro ⟨hc,hi⟩
    exact hf.left_barrier he hi hc.symm
  simp only [ite_eq_right hm]

omit [NeZero q] in
lemma total_last {f : Fin N → Cell q} (h : Fin N) (j : Fin q)
    (he : (f h).skeleton.rightExternal) :
    total S f h j=leftSum S f h j+(f h).delta (S.clause (f h).metadata.task j) := by
  classical
  have hi : ∀ i : Fin N,
      (if SameRegion f h i ∧ i.val < N then (f i).delta (S.clause (f h).metadata.task j) else 0) =
      (if SameRegion f h i ∧ i.val < h.val then (f i).delta (S.clause (f h).metadata.task j) else 0)+
      if i=h then (f h).delta (S.clause (f h).metadata.task j) else 0 := by
    intro i
    by_cases hic : SameRegion f h i
    · by_cases hie : i=h
      · subst i; simp [hic]
      · have hih : i.val < h.val := by
          have hn := Fin.val_ne_of_ne hie
          by_contra hn'
          exact hic.right_barrier (by omega) he
        simp [hic,hih,hie]
    · have hne : i≠h := by intro he; subst i; exact hic (Connected.refl _ _)
      simp [hic,hne]
  simp only [total,leftSum,sum,hi,Finset.sum_add_distrib]
  simp

lemma good_initial (f : Fin N → Cell q) (h : Fin N)
    (hp : (f h).head.phase=.acquisition) (hj : (f h).head.clause=0) (hr : (f h).head.reg=0) :
    Good S f h := by simp [Good,hp,hj,hr,potential,passed]

omit [NeZero q] in
lemma good_congr {f g : Fin N → Cell q} {h k : Fin N}
    (ht : (f h).metadata.task=(g k).metadata.task) (hh : (f h).head=(g k).head)
    (hT : ∀ j, total S f h j=total S g k j)
    (hL : ∀ j, leftSum S f h j=leftSum S g k j) : Good S f h ↔ Good S g k := by
  have hp : ∀ j p, potential S f h j p=potential S g k j p := by
    intro j p; cases p <;> simp only [potential,hT,hL]
  simp only [Good,hh,hp,ht,holds,hT]

omit [NeZero q] in
lemma good_same_cuts {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {h : Fin N} (hh : (f h).skeleton.IsHead)
    (hc : ∀ i, cellCut f i ↔ cellCut g i) (he : f h=g h)
    (hr : ∀ i, (f i).LockedReads (g i)) : Good S f h ↔ Good S g h := by
  have hk : (g h).skeleton.IsHead := he ▸ hh
  have hs := sum_congr S hf hg hh hk (fun _ => Connected.congr hc)
    (congrArg (fun c : Cell q => c.metadata.task) he) hr
  exact good_congr S (congrArg (fun c : Cell q => c.metadata.task) he)
    (congrArg Cell.head he) (fun j => hs j N) (fun j => hs j h.val)

omit [NeZero q] in
lemma good_semanticZero {f : Fin N → Cell q} {h : Fin N}
    (hg : Good S f h) (hz : SemanticZero S (f h)) :
    (f h).head.phase=.success ∧ (f h).metadata.zeroTask=true := by
  rcases hz.2 with ⟨hp,hr⟩ | ⟨hp,hf⟩ | hh
  · exfalso
    apply hr
    rcases hp with hp | hp | hp <;>
      simpa only [hp,potential] using hg.1
  · exfalso
    have hh := hg.2
    simp only [hp,reduceCtorEq,ite_false,passed,true_implies] at hh
    have htruth := hh.2
    unfold holds at htruth
    have hr : (f h).head.reg=total S f h (f h).head.clause := by
      simpa only [hp,potential] using hg.1
    rw [hr,htruth] at hf
    cases hf
  · exact hh

omit [NeZero q] in
lemma allGood_of_idle (f : Fin N → Cell q) (hf : ∀ i, (f i).marker=.idle) : AllGood S f := by
  intro h hh; simp [hf h] at hh

omit [NeZero q] in
lemma allGood_single {f g : Fin N → Cell q} (i : Fin N)
    (hf : ∀ h, h≠i → f h=g h)
    (ho : ∀ h, h≠i → (f h).marker=.full → (Good S f h ↔ Good S g h))
    (hi : ((f i).marker=.full → Good S f i) ↔ ((g i).marker=.full → Good S g i)) :
    AllGood S f ↔ AllGood S g := by
  constructor
  · intro hh h hm
    by_cases he : h=i
    · subst h; exact hi.mp (hh i) hm
    · have hm' : (f h).marker=.full := by rw [hf h he]; exact hm
      exact (ho h he hm').mp (hh h hm')
  · intro hh h hm
    by_cases he : h=i
    · subst h; exact hi.mpr (hh i) hm
    · have hm' : (g h).marker=.full := by rw [←hf h he]; exact hm
      exact (ho h he hm).mpr (hh h hm')

omit [NeZero q] in
lemma allGood_pair {f g : Fin N → Cell q} (i j : Fin N)
    (hf : ∀ h, h≠i → h≠j → f h=g h)
    (ho : ∀ h, h≠i → h≠j → (f h).marker=.full → (Good S f h ↔ Good S g h))
    (hi : (((f i).marker=.full → Good S f i) ∧ ((f j).marker=.full → Good S f j)) ↔
      (((g i).marker=.full → Good S g i) ∧ ((g j).marker=.full → Good S g j))) :
    AllGood S f ↔ AllGood S g := by
  constructor
  · intro hh h hm
    by_cases he : h=i
    · subst h; exact (hi.mp ⟨hh i,hh j⟩).1 hm
    · by_cases he' : h=j
      · subst h; exact (hi.mp ⟨hh i,hh j⟩).2 hm
      · have hm' : (f h).marker=.full := by rw [hf h he he']; exact hm
        exact (ho h he he' hm').mp (hh h hm')
  · intro hh h hm
    by_cases he : h=i
    · subst h; exact (hi.mpr ⟨hh i,hh j⟩).1 hm
    · by_cases he' : h=j
      · subst h; exact (hi.mpr ⟨hh i,hh j⟩).2 hm
      · have hm' : (g h).marker=.full := by rw [←hf h he he']; exact hm
        exact (ho h he he' hm).mpr (hh h hm')

omit [NeZero q] in
lemma total_eq_left_of_last {f : Fin N → Cell q} (i : Fin N) (j : Fin q)
    (hm : (f i).marker≠.left) (hl : (f i).skeleton.last) :
    total S f i j=leftSum S f i j := by
  have he := total_last S i j (Or.inr (Or.inr ⟨hm,hl⟩))
  rw [Cell.delta_stop _ _ hl.2,add_zero] at he
  exact he

omit [NeZero q] in
lemma leftSum_eq_zero_of_first {f : Fin N → Cell q} (hf : Coherent f) (i : Fin N) (j : Fin q)
    (hm : (f i).marker≠.right) (hl : (f i).skeleton.first) :
    leftSum S f i j=0 := leftSum_first S hf i j (Or.inr ⟨hm,hl⟩)

lemma unary_full_sums {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) {c : Cell q} {b b' : Bool}
    {j j' : Fin q} {p p' : Phase} {r r' : Reg}
    (hfi : f i=c.full b j p r) (hgi : g i=c.full b' j' p' r') :
    (∀ t, total S g i t=total S f i t) ∧
    (∀ t, leftSum S g i t=leftSum S f i t) := by
  have hs := sum_congr S hf hg (h:=i) (k:=i)
    (Or.inr (by simp [hfi,Cell.full,Skeleton.mark]))
    (Or.inr (by simp [hgi,Cell.full,Skeleton.mark]))
    (fun _ => Connected.congr hu.cuts)
    (by simp [hfi,hgi,Cell.full,Cell.metadata,Skeleton.mark]) hu.reads
  exact ⟨fun t => (hs t N).symm,fun t => (hs t i.val).symm⟩

omit [NeZero q] in
lemma below_next {P : Fin q → Prop} (i j : Fin q) (hij : i.val+1=j.val) :
    (∀ k : Fin q, k.val < j.val → P k) ↔ (∀ k : Fin q, k.val < i.val → P k) ∧ P i := by
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega),h i (by omega)⟩
  · rintro ⟨h,hi⟩ k hk
    by_cases he : k=i
    · simpa only [he] using hi
    · apply h k
      have := Fin.val_ne_of_ne he
      omega

omit [NeZero q] in
lemma below_success {P : Fin q → Prop} (i : Fin q) (m : ℕ) (hij : i.val+1=m) :
    (∀ k : Fin q, k.val < m → P k) ↔ (∀ k : Fin q, k.val < i.val → P k) ∧ P i := by
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega),h i (by omega)⟩
  · rintro ⟨h,hi⟩ k hk
    by_cases he : k=i
    · simpa only [he] using hi
    · apply h k
      have := Fin.val_ne_of_ne he
      omega

lemma unary_local {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) :
    ((f i).marker=.full → Good S f i) ↔ ((g i).marker=.full → Good S g i) := by
  have he := hu.edge
  generalize hfi : f i=a at he
  generalize hgi : g i=b at he
  cases he with
  | create c b hc => simp [Cell.marker,Cell.boundary,Cell.idle,Skeleton.mark]
  | finish_acquisition c b hc =>
    have hgood : Good S g i := good_initial S g i (by simp [hgi,Cell.full])
      (by simp [hgi,Cell.full]) (by simp [hgi,Cell.full])
    simp [Cell.marker,Cell.boundary,Cell.full,Skeleton.mark,hgood]
  | read_enter c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    have hh : total S f i j=leftSum S f i j := total_eq_left_of_last S i j
      (by simp [hfi,Cell.marker,Cell.full,Skeleton.mark]) (by simpa [hfi,Cell.full] using hl)
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,hL,hh,holds]
  | read_turn c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    have hh : leftSum S f i j=0 := leftSum_eq_zero_of_first S hf i j
      (by simp [hfi,Cell.marker,Cell.full,Skeleton.mark]) (by simpa [hfi,Cell.full] using hl)
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,hh,holds]
  | read_exit c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,holds]
  | gate c b j r hl htruth =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp only [hfi,hgi,Cell.marker,Cell.full,Skeleton.mark,Good,Cell.metadata,potential,
      passed,reduceCtorEq,true_implies,ite_false,false_implies,and_true,hT,holds]
    constructor
    · rintro ⟨hr,hh⟩
      exact ⟨hr,hh,hr ▸ htruth⟩
    · rintro ⟨hr,hh,_⟩; exact ⟨hr,hh⟩
  | undo_enter c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,holds]
  | undo_turn c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    have hh : leftSum S f i j=0 := leftSum_eq_zero_of_first S hf i j
      (by simp [hfi,Cell.marker,Cell.full,Skeleton.mark]) (by simpa [hfi,Cell.full] using hl)
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,hL,hh,holds]
  | undo_exit c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    have hh : total S f i j=leftSum S f i j := total_eq_left_of_last S i j
      (by simp [hfi,Cell.marker,Cell.full,Skeleton.mark]) (by simpa [hfi,Cell.full] using hl)
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,hh,holds,
      CharTwo.add_self_eq_zero]
  | next c b j j' hj hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp only [hfi,hgi,Cell.marker,Cell.full,Skeleton.mark,Good,Cell.metadata,potential,
      passed,reduceCtorEq,true_implies,ite_false,false_implies,and_true,true_and,hT,holds]
    exact (below_next j j' hj).symm
  | success c b j hj hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp only [hfi,hgi,Cell.marker,Cell.full,Skeleton.mark,Good,Cell.metadata,potential,
      passed,reduceCtorEq,true_implies,ite_false,ite_true,true_and,hT,holds]
    exact (below_success j (S.count c.metadata.task).val hj).symm
  | pivot c b hl ht =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,hT,holds]

lemma allGood_unary {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) : AllGood S f ↔ AllGood S g := by
  apply allGood_single S i hu.off _ (unary_local S hf hg hu)
  intro h hne hh
  exact good_same_cuts S hf hg (Or.inr hh) hu.cuts (hu.off h hne) hu.reads
omit [NeZero q] in
lemma allGood_fields {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    (hc : ∀ i, cellCut f i ↔ cellCut g i)
    (hr : ∀ i, (f i).LockedReads (g i))
    (hm : ∀ i, (f i).marker=(g i).marker)
    (ht : ∀ i, (f i).metadata.task=(g i).metadata.task)
    (hh : ∀ i, (f i).head=(g i).head) : AllGood S f ↔ AllGood S g := by
  have he (i : Fin N) (hi : (f i).marker=.full) : Good S f i ↔ Good S g i := by
    have hs := sum_congr S hf hg (Or.inr hi) (Or.inr ((hm i).symm.trans hi))
      (fun _ => Connected.congr hc) (ht i) hr
    exact good_congr S (ht i) (hh i) (fun j => hs j N) (fun j => hs j i.val)
  constructor
  · intro h i hi; have hi' : (f i).marker=.full := (hm i).trans hi
    exact (he i hi').mp (h i hi')
  · intro h i hi; exact (he i hi).mpr (h i ((hm i) ▸ hi))

omit [NeZero q] in
lemma moving_sum_congr {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {h k : Fin N} (hhead : (f h).skeleton.IsHead) (khead : (g k).skeleton.IsHead)
    (hc : ∀ i, cellCut f i ↔ cellCut g i) (hconn : SameRegion f h k)
    (ht : (f h).metadata.task=(g k).metadata.task)
    (hr : ∀ i, (f i).LockedReads (g i)) (t : Fin q) (v : ℕ) :
    sum S f h t v=sum S g k t v := by
  apply sum_congr S hf hg hhead khead _ ht hr t v
  intro l
  change Connected (cellCut f) h l ↔ Connected (cellCut g) k l
  rw [←Connected.congr hc]
  exact ⟨fun hh => hconn.symm.trans hh,fun hh => hconn.trans hh⟩

omit [NeZero q] in
lemma move_sums {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j h k : Fin N} (ha : i.val+1=j.val)
    (hhead : (f h).skeleton.IsHead) (khead : (g k).skeleton.IsHead)
    (hc : ∀ i, cellCut f i ↔ cellCut g i) (hconn : SameRegion f h k)
    (hci : SameRegion f h i)
    (ht : (f h).metadata.task=(g k).metadata.task)
    (hr : ∀ i, (f i).LockedReads (g i)) :
    (∀ t, total S f h t=total S g k t) ∧
    (∀ t, sum S f h t j.val=sum S g k t i.val+(f i).delta (S.clause (f h).metadata.task t)) := by
  have hs := sum_congr S hf hg hhead khead (fun l => by
    change Connected (cellCut f) h l ↔ Connected (cellCut g) k l
    rw [←Connected.congr hc]
    exact ⟨fun hh => hconn.symm.trans hh,fun hh => hconn.trans hh⟩) ht hr
  refine ⟨fun t => hs t N,fun t => ?_⟩
  rw [←ha,sum_succ,ite_eq_left hci,hs]

omit [NeZero q] in
lemma good_read_left {f g : Fin N → Cell q} {i j : Fin N} {a b : Cell q}
    {s : Bool} {c : Fin q} {r δ : Reg}
    (hf : f j=b.full s c .readLeft r) (hg : g i=a.full s c .readLeft (r+δ))
    (ht : (f j).metadata.task=(g i).metadata.task)
    (hT : ∀ t, total S f j t=total S g i t)
    (hL : leftSum S f j c=leftSum S g i c+δ) : Good S f j ↔ Good S g i := by
  have he : r=total S f j c-leftSum S f j c ↔
      r+δ=total S g i c-leftSum S g i c := by
    rw [hT,hL]
    constructor
    · intro hr; rw [hr]; abel
    · intro hr
      apply add_right_cancel (b:=δ)
      rw [hr]; abel
  simp only [Good,hf,hg,Cell.full,reduceCtorEq,ite_false,potential,passed,false_implies,and_true]
  change (r=total S f j c-leftSum S f j c ∧ _) ↔
    (r+δ=total S g i c-leftSum S g i c ∧ _)
  rw [he]
  simp only [holds,ht,hT]

omit [NeZero q] in
lemma good_undo_right {f g : Fin N → Cell q} {i j : Fin N} {a b : Cell q}
    {s : Bool} {c : Fin q} {r δ : Reg}
    (hf : f i=a.full s c .undoRight r) (hg : g j=b.full s c .undoRight (r+δ))
    (ht : (f i).metadata.task=(g j).metadata.task)
    (hT : ∀ t, total S f i t=total S g j t)
    (hL : leftSum S g j c=leftSum S f i c+δ) : Good S f i ↔ Good S g j := by
  have he : r=total S f i c+leftSum S f i c ↔
      r+δ=total S g j c+leftSum S g j c := by
    rw [hT,hL,←add_assoc,add_left_inj]
  simp only [Good,hf,hg,Cell.full,reduceCtorEq,ite_false,potential,passed,true_implies]
  change (r=total S f i c+leftSum S f i c ∧ _) ↔
    (r+δ=total S g j c+leftSum S g j c ∧ _)
  rw [he]
  simp only [holds,ht,hT]

omit [NeZero q] in
lemma good_other_move {f g : Fin N → Cell q} {i j : Fin N}
    (ht : (f i).metadata.task=(g j).metadata.task) (hh : (f i).head=(g j).head)
    (hp : (f i).head.phase=.readRight ∨ (f i).head.phase=.undoLeft)
    (hT : ∀ t, total S f i t=total S g j t) : Good S f i ↔ Good S g j := by
  have hp' := hp
  rw [hh] at hp'
  rcases hp' with hp' | hp' <;>
    simp only [Good,hh,hp',potential,passed,false_implies,true_implies,reduceCtorEq,ite_false,
      holds,ht,hT]

lemma allGood_binary_cuts {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) (hc : ∀ h, cellCut f h ↔ cellCut g h)
    (hl : (((f i).marker=.full → Good S f i) ∧ ((f j).marker=.full → Good S f j)) ↔
      (((g i).marker=.full → Good S g i) ∧ ((g j).marker=.full → Good S g j))) :
    AllGood S f ↔ AllGood S g := by
  apply allGood_pair S i j hb.off _ hl
  intro h hi hj hh
  exact good_same_cuts S hf hg (Or.inr hh) hc (hb.off h hi hj) hb.reads

end Verification
end SourceBurnside.FiniteTable
end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_CommittedWords
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instTransCellGeomRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]
namespace Verification
open scoped BigOperators
variable (S : Schedule q)
lemma binary_acquire_good {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool}
    (hfi : f i=a.boundary s) (hfj : f j=b.idle s)
    (hgi : g i=a.wing .left) (hgj : g j=b.boundary s) : AllGood S f ↔ AllGood S g := by
  apply allGood_pair S i j hb.off _ (by
    simp [hfi,hfj,hgi,hgj,Cell.marker,Cell.boundary,Cell.wing,Cell.idle,Skeleton.mark])
  intro h hi hj hh
  have ha : ¬SameRegion f h i := by
    intro hc
    exact hi (hf.unique_head (Or.inr hh) (Or.inl (by simp [hfi,Cell.boundary,Skeleton.mark])) hc)
  have hb' : ¬SameRegion f h j := by
    intro hc
    exact hj (hf.idle_component (by simp [hfj,Cell.marker,Cell.idle]) hc)
  have hcuts : ∀ h, h≠i → (cellCut f h ↔ cellCut g h) := hb.cuts_off (by
    simp [cellCut,hfj,hgj,Cell.idle,Cell.boundary,Skeleton.rightExternal,Skeleton.mark])
  have hcomp (k : Fin N) : SameRegion f h k ↔ SameRegion g h k :=
    Connected.edit_unrelated hb.adjacent hcuts ha hb'
  have hh' : (g h).skeleton.IsHead := by rw [←hb.off h hi hj]; exact Or.inr hh
  have hs := sum_congr S hf hg (Or.inr hh) hh' hcomp
    (congrArg (fun c : Cell q => c.metadata.task) (hb.off h hi hj)) hb.reads
  exact good_congr S (congrArg (fun c : Cell q => c.metadata.task) (hb.off h hi hj))
    (congrArg Cell.head (hb.off h hi hj)) (fun t => hs t N) (fun t => hs t h.val)

lemma binary_read_left_good {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool} {c : Fin q} {r : Reg}
    (hp : Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right))
    (hfi : f i=a.wing .left) (hfj : f j=b.full s c .readLeft r)
    (hgi : g i=a.full s c .readLeft (r+a.delta (S.clause a.metadata.task c)))
    (hgj : g j=b.wing .right) : AllGood S f ↔ AllGood S g := by
  have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
    (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
    (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
  have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
    simp [cellCut,hfi,Cell.wing,Skeleton.rightExternal])
  have ht := SameRegion.task hf hconn.symm
  have ht' : (f j).metadata.task=(g i).metadata.task := by
    simpa [hfi,hgi,Cell.wing,Cell.full,Cell.metadata,Skeleton.mark] using ht
  obtain ⟨hT,hL⟩ := move_sums S hf hg hb.adjacent
    (h:=j) (k:=i) (by simp [hfj,Cell.full,Skeleton.IsHead])
    (by simp [hgi,Cell.full,Skeleton.IsHead]) hc hconn.symm hconn.symm ht' hb.reads
  have hdelta : (f i).delta (S.clause (f j).metadata.task c)=a.delta (S.clause a.metadata.task c) := by
    rw [ht,hfi]
    rfl
  have hL' : leftSum S f j c=leftSum S g i c+a.delta (S.clause a.metadata.task c) := by
    simpa only [leftSum,hdelta] using hL c
  apply allGood_binary_cuts S hf hg hb hc
  simpa only [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark_marker,
    reduceCtorEq,false_implies,true_implies,true_and,and_true] using
    good_read_left S hfj hgi ht' hT hL'

lemma binary_read_right_good {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool} {c : Fin q} {r : Reg}
    (hp : Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right))
    (hfi : f i=a.full s c .readRight r) (hfj : f j=b.wing .right)
    (hgi : g i=a.wing .left) (hgj : g j=b.full s c .readRight r) : AllGood S f ↔ AllGood S g := by
  have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
    (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
    (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
  have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
    simp [cellCut,hfi,Cell.full,Skeleton.rightExternal,full_conditions hp])
  have ht := SameRegion.task hf hconn
  have ht' : (f i).metadata.task=(g j).metadata.task := by
    simpa [hfj,hgj,Cell.wing,Cell.full,Cell.metadata,Skeleton.mark] using ht
  obtain ⟨hT,_⟩ := move_sums S hf hg hb.adjacent
    (h:=i) (k:=j) (by simp [hfi,Cell.full,Skeleton.IsHead])
    (by simp [hgj,Cell.full,Skeleton.IsHead]) hc hconn (Connected.refl _ _) ht' hb.reads
  have he := good_other_move S ht' (by simp [hfi,hgj,Cell.full])
    (Or.inl (by simp [hfi,Cell.full])) hT
  apply allGood_binary_cuts S hf hg hb hc
  simpa only [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark_marker,
    reduceCtorEq,false_implies,true_implies,true_and,and_true] using he

lemma binary_undo_left_good {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool} {c : Fin q} {r : Reg}
    (hp : Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right))
    (hfi : f i=a.wing .left) (hfj : f j=b.full s c .undoLeft r)
    (hgi : g i=a.full s c .undoLeft r) (hgj : g j=b.wing .right) : AllGood S f ↔ AllGood S g := by
  have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
    (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
    (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
  have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
    simp [cellCut,hfi,Cell.wing,Skeleton.rightExternal])
  have ht := SameRegion.task hf hconn.symm
  have ht' : (f j).metadata.task=(g i).metadata.task := by
    simpa [hfi,hgi,Cell.wing,Cell.full,Cell.metadata,Skeleton.mark] using ht
  have hs := moving_sum_congr S hf hg (h:=j) (k:=i)
    (by simp [hfj,Cell.full,Skeleton.IsHead]) (by simp [hgi,Cell.full,Skeleton.IsHead])
    hc hconn.symm ht' hb.reads
  have he := good_other_move S ht' (by simp [hfj,hgi,Cell.full])
    (Or.inr (by simp [hfj,Cell.full])) (fun t => hs t N)
  apply allGood_binary_cuts S hf hg hb hc
  simpa only [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark_marker,
    reduceCtorEq,false_implies,true_implies,true_and,and_true] using he

lemma binary_undo_right_good {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool} {c : Fin q} {r : Reg}
    (hp : Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right))
    (hfi : f i=a.full s c .undoRight r) (hfj : f j=b.wing .right)
    (hgi : g i=a.wing .left)
    (hgj : g j=b.full s c .undoRight (r+a.delta (S.clause a.metadata.task c))) :
    AllGood S f ↔ AllGood S g := by
  have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
    (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
    (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
  have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
    simp [cellCut,hfi,Cell.full,Skeleton.rightExternal,full_conditions hp])
  have ht := SameRegion.task hf hconn
  have ht' : (f i).metadata.task=(g j).metadata.task := by
    simpa [hfj,hgj,Cell.wing,Cell.full,Cell.metadata,Skeleton.mark] using ht
  have hs := moving_sum_congr S hf hg (h:=i) (k:=j)
    (by simp [hfi,Cell.full,Skeleton.IsHead]) (by simp [hgj,Cell.full,Skeleton.IsHead])
    hc hconn ht' hb.reads
  have hL : leftSum S g j c=leftSum S f i c+a.delta (S.clause a.metadata.task c) := by
    unfold leftSum
    rw [←hs,←hb.adjacent,sum_succ,ite_eq_left (Connected.refl _ _)]
    rw [hfi]
    rfl
  have he := good_undo_right S hfi hgj ht' (fun t => hs t N) hL
  apply allGood_binary_cuts S hf hg hb hc
  simpa only [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark_marker,
    reduceCtorEq,false_implies,true_implies,true_and,and_true] using he

lemma allGood_binary_fields {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j)
    (hci : cellCut f i ↔ cellCut g i) (hcj : cellCut f j ↔ cellCut g j)
    (hmi : (f i).marker=(g i).marker) (hmj : (f j).marker=(g j).marker)
    (hti : (f i).metadata.task=(g i).metadata.task) (htj : (f j).metadata.task=(g j).metadata.task)
    (hhi : (f i).head=(g i).head) (hhj : (f j).head=(g j).head) :
    AllGood S f ↔ AllGood S g := by
  apply allGood_fields S hf hg (hb.cuts hci hcj) hb.reads
  all_goals
    intro h
    by_cases he : h=i
    · subst h; assumption
    · by_cases he' : h=j
      · subst h; assumption
      · rw [hb.off h he he']

lemma allGood_binary {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) : AllGood S f ↔ AllGood S g := by
  have he := hb.edge
  generalize hfi : f i=a at he
  generalize hfj : f j=b at he
  generalize hgi : g i=a' at he
  generalize hgj : g j=b' at he
  cases he with
  | acquire a b s hp => exact binary_acquire_good S hf hg hb hfi hfj hgi hgj
  | read_left a b s c r hp => exact binary_read_left_good S hf hg hb hp hfi hfj hgi hgj
  | read_right a b s c r hp => exact binary_read_right_good S hf hg hb hp hfi hfj hgi hgj
  | undo_left a b s c r hp => exact binary_undo_left_good S hf hg hb hp hfi hfj hgi hgj
  | undo_right a b s c r hp => exact binary_undo_right_good S hf hg hb hp hfi hfj hgi hgj
  | checker_create a b p x ha hp hb' =>
    apply allGood_binary_fields S hf hg hb <;> simp [hfi,hfj,hgi,hgj,cellCut,Cell.setChecker,
      Cell.marker,Cell.metadata]
  | checker_advance a b v x ha hb' hv =>
    apply allGood_binary_fields S hf hg hb <;> simp [hfi,hfj,hgi,hgj,cellCut,Cell.setChecker,
      Cell.marker,Cell.metadata]
  | swap a b x y ha hb' hab hna hnb =>
    have hcut : a.skeleton.rightExternal ↔ b.skeleton.rightExternal := by
      rw [←hab]
      simp [Skeleton.rightExternal,Skeleton.last,Cell.setColor,Cell.pos] at ha ⊢
      simp [ha]
    have hcuts := hb.cuts (by simpa [cellCut,hfi,hgi] using hcut)
      (by simpa [cellCut,hfj,hgj] using hcut.symm)
    apply allGood_binary_cuts S hf hg hb hcuts
    have hna' : a.marker≠.full := fun hh => hna.1 (Or.inr hh)
    have hnb' : b.marker≠.full := fun hh => hnb.1 (Or.inr hh)
    simp [hfi,hfj,hgi,hgj,hna',hnb']

omit [NeZero q] in
lemma allGood_cast {M : ℕ} (he : M=N) (f : Fin M → Cell q) :
    AllGood S (fun i : Fin N => f (Fin.cast he.symm i)) ↔ AllGood S f := by
  subst N
  rfl

omit [NeZero q] in
lemma wordGood_ofFn (f : Fin N → Cell q) : WordGood S (List.ofFn f) ↔ AllGood S f := by
  unfold WordGood
  have he : (List.ofFn f).get = fun i => f (Fin.cast (List.length_ofFn) i) := by
    funext i; exact List.get_ofFn f i
  rw [he]
  exact allGood_cast S (List.length_ofFn).symm f

omit [NeZero q] in
lemma get_of_context {f : Fin N → Cell q} {p s a : List (Cell q)}
    (hf : List.ofFn f=p++a++s) (i : Fin N) (k : ℕ) (hk : k < a.length)
    (hi : i.val=p.length+k) : f i=a[k] := by
  have hh := congrArg (fun l : List (Cell q) => l[i.val]?) hf
  simp only [List.getElem?_ofFn,dite_eq_left i.isLt,List.append_assoc] at hh
  have hn : ¬ i.val < p.length := by omega
  have he : i.val-p.length=k := by omega
  rw [List.getElem?_append,ite_eq_right hn,he,List.getElem?_append,
    ite_eq_left hk,List.getElem?_eq_getElem hk] at hh
  exact Option.some.inj hh

omit [NeZero q] in
lemma off_of_context {f g : Fin N → Cell q} {p s a b : List (Cell q)}
    (hf : List.ofFn f=p++a++s) (hg : List.ofFn g=p++b++s) (hab : a.length=b.length)
    (i : Fin N) (hi : i.val < p.length ∨ p.length+a.length ≤ i.val) : f i=g i := by
  have hf' := congrArg (fun l : List (Cell q) => l[i.val]?) hf
  have hg' := congrArg (fun l : List (Cell q) => l[i.val]?) hg
  simp only [List.getElem?_ofFn,dite_eq_left i.isLt,List.append_assoc] at hf' hg'
  have hh : (p++(a++s))[i.val]?=(p++(b++s))[i.val]? := by
    rcases hi with hi | hi
    · simp only [List.getElem?_append,ite_eq_left hi]
    · have hp : ¬ i.val < p.length := by omega
      have ha : ¬ i.val-p.length < a.length := by omega
      have hb : ¬ i.val-p.length < b.length := by omega
      simp only [List.getElem?_append,ite_eq_right hp,ite_eq_right hb,hab]
  exact Option.some.inj (hf'.trans (hh.trans hg'.symm))

lemma unary_context_good {f g : Fin N → Cell q} {p s : List (Cell q)} {a b : Cell q}
    (hf : Coherent f) (hg : Coherent g)
    (hfv : List.ofFn f=p++[a]++s) (hgv : List.ofFn g=p++[b]++s) (he : Unary S a b) :
    AllGood S f ↔ AllGood S g := by
  have hn := congrArg List.length hfv
  simp only [List.length_ofFn,List.length_append,List.length_singleton] at hn
  let i : Fin N := ⟨p.length,by omega⟩
  have hfi : f i=a := by simpa using get_of_context hfv i 0 (by simp) (by simp [i])
  have hgi : g i=b := by simpa using get_of_context hgv i 0 (by simp) (by simp [i])
  apply allGood_unary S hf hg (i:=i)
  constructor
  · intro h hne
    apply off_of_context hfv hgv rfl h
    have hn : h.val≠p.length := fun hh => hne (Fin.ext hh)
    simp only [List.length_singleton]
    omega
  · simpa [hfi,hgi] using he

lemma binary_context_good {f g : Fin N → Cell q} {p s : List (Cell q)} {a b a' b' : Cell q}
    (hf : Coherent f) (hg : Coherent g)
    (hfv : List.ofFn f=p++[a,b]++s) (hgv : List.ofFn g=p++[a',b']++s)
    (he : Binary S a b a' b') : AllGood S f ↔ AllGood S g := by
  have hn := congrArg List.length hfv
  simp only [List.length_ofFn,List.length_append,List.length_cons,List.length_nil] at hn
  let i : Fin N := ⟨p.length,by omega⟩
  let j : Fin N := ⟨p.length+1,by omega⟩
  have hfi : f i=a := by simpa using get_of_context hfv i 0 (by simp) (by simp [i])
  have hfj : f j=b := by simpa using get_of_context hfv j 1 (by simp) (by simp [j])
  have hgi : g i=a' := by simpa using get_of_context hgv i 0 (by simp) (by simp [i])
  have hgj : g j=b' := by simpa using get_of_context hgv j 1 (by simp) (by simp [j])
  apply allGood_binary S hf hg (i:=i) (j:=j)
  constructor
  · rfl
  · intro h hne hne'
    apply off_of_context hfv hgv rfl h
    have hni : h.val≠p.length := fun hh => hne (Fin.ext hh)
    have hnj : h.val≠p.length+1 := fun hh => hne' (Fin.ext hh)
    simp only [List.length_cons,List.length_nil]
    omega
  · simpa [hfi,hfj,hgi,hgj] using he

lemma allGood_step {f g : Fin N → Cell q} {d : ℕ} (hf : Syntax S d (List.ofFn f))
    (he : Step S d (List.ofFn f) (List.ofFn g)) : AllGood S f ↔ AllGood S g := by
  have hg := reach_syntax (Relation.ReflTransGen.single he) hf
  have hf' := coherent_of_syntax S hf
  have hg' := coherent_of_syntax S hg
  obtain ⟨p,s,v,w,hf,hg,hh⟩ := he
  rcases hh.2 with ⟨a,b,rfl,rfl,he⟩ | ⟨a,b,a',b',rfl,rfl,he⟩
  · rcases he with he | he
    · exact unary_context_good S hf' hg' hf hg he
    · exact (unary_context_good S hg' hf' hg hf he).symm
  · rcases he with he | he
    · exact binary_context_good S hf' hg' hf hg he
    · exact (binary_context_good S hg' hf' hg hf he).symm

lemma wordGood_step {v w : List (Cell q)} {d : ℕ} (hv : Syntax S d v)
    (he : Step S d v w) : WordGood S v ↔ WordGood S w := by
  let f := v.get
  have hl := step_length he
  let g : Fin v.length → Cell q := fun i => w.get (Fin.cast hl i)
  have hfv : List.ofFn f=v := List.ofFn_get v
  have hgw : List.ofFn g=w := by
    rw [show g=(fun i => w.get (Fin.cast hl i)) from rfl,←List.ofFn_congr hl.symm w.get]
    exact List.ofFn_get w
  rw [←hfv] at hv
  rw [←hfv,←hgw] at he ⊢
  rw [wordGood_ofFn,wordGood_ofFn]
  exact allGood_step S hv he

theorem wordGood_reach {v w : List (Cell q)} {d : ℕ} (hv : Syntax S d v)
    (he : Reach S d v w) : WordGood S v ↔ WordGood S w := by
  induction he with
  | refl => rfl
  | tail h e ih => exact ih.trans (wordGood_step S (reach_syntax h hv) e)

end Verification

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]

namespace Connected
lemma mono {cut cut' : Fin N → Prop} {i j : Fin N}
    (hcut : ∀ k, cut' k → cut k) (h : Connected cut i j) : Connected cut' i j := by
  intro k hk hk' hc
  exact h k hk hk' (hcut k hc)
end Connected

lemma BinaryAt.everywhere {S : Schedule q} {f g : Fin N → Cell q} {i j : Fin N}
    (hb : BinaryAt S f g i j) {P : Cell q → Cell q → Prop} (hrefl : ∀ a, P a a)
    (hi : P (f i) (g i)) (hj : P (f j) (g j)) : ∀ h, P (f h) (g h) := by
  intro h
  by_cases he : h=i
  · simpa [he] using hi
  · by_cases he' : h=j
    · simpa [he'] using hj
    · rw [hb.off h he he']; exact hrefl _

namespace Committed

omit [NeZero q] in
lemma idle {f : Fin N → Cell q} {i : Fin N} (hi : (f i).marker=.idle) :
    value f i=(f i).data false := by simp [value,hi]

omit [NeZero q] in
lemma owned {f : Fin N → Cell q} (hf : Coherent f) {i h : Fin N} (hh : Own f i h) :
    value f i=(f i).data (f h).head.side := by
  classical
  have hi : (f i).marker≠.idle := hf.region_locked hh.2 hh.1
  have he : ∃ k, Own f i k := ⟨h,hh⟩
  have hch := Classical.choose_spec he
  have heq : Classical.choose he=h :=
    hf.unique_head hch.2 hh.2 (hch.1.symm.trans hh.1)
  simp only [value,ite_eq_right hi,dite_eq_left he,heq]

omit [NeZero q] in
lemma congr {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g) (i : Fin N)
    (hi : (f i).marker=.idle ↔ (g i).marker=.idle)
    (hdi : (f i).marker=.idle → (f i).data false=(g i).data false)
    (ho : ∀ h, Own f i h → ∃ k, Own g i k ∧ (f i).data (f h).head.side=(g i).data (g k).head.side)
    (hn : (∃ k, Own g i k) → ∃ h, Own f i h) : value f i=value g i := by
  classical
  by_cases hid : (f i).marker=.idle
  · rw [idle hid,idle (hi.mp hid)]
    exact hdi hid
  · by_cases he : ∃ h, Own f i h
    · obtain ⟨h,hh⟩ := he
      obtain ⟨k,hk,heq⟩ := ho h hh
      rw [owned hf hh,owned hg hk]
      exact heq
    · have he' : ¬∃ k, Own g i k := fun hh => he (hn hh)
      simp only [value,ite_eq_right hid,ite_eq_right ((not_congr hi).mp hid),dite_eq_right he,dite_eq_right he']

omit [NeZero q] in
lemma fields {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g) (i : Fin N)
    (hc : ∀ h, SameRegion f i h ↔ SameRegion g i h)
    (hi : (f i).marker=.idle ↔ (g i).marker=.idle)
    (hd : (f i).data=(g i).data)
    (hh : ∀ h, SameRegion f i h → ((f h).skeleton.IsHead ↔ (g h).skeleton.IsHead))
    (hs : ∀ h, Own f i h → (f h).head.side=(g h).head.side) : value f i=value g i := by
  apply congr hf hg i hi (fun _ => congrFun hd false)
  · intro h ho
    exact ⟨h,⟨(hc h).mp ho.1,(hh h ho.1).mp ho.2⟩,by rw [hd,hs h ho]⟩
  · rintro ⟨h,hh'⟩
    have hhc := (hc h).mpr hh'.1
    exact ⟨h,hhc,(hh h hhc).mpr hh'.2⟩

omit [NeZero q] in
lemma same_cuts_fields {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    (hc : ∀ i, cellCut f i ↔ cellCut g i)
    (hi : ∀ i, (f i).marker=.idle ↔ (g i).marker=.idle)
    (hd : ∀ i, (f i).data=(g i).data)
    (hh : ∀ i, (f i).skeleton.IsHead ↔ (g i).skeleton.IsHead)
    (hs : ∀ i, (f i).skeleton.IsHead → (f i).head.side=(g i).head.side) :
    ∀ i, value f i=value g i := by
  intro i
  exact fields hf hg i (fun _ => Connected.congr hc) (hi i) (hd i)
    (fun h _ => hh h) (fun h ho => hs h ho.2)

lemma unary_fields {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i)
    (hi : (f i).marker=.idle ↔ (g i).marker=.idle) (hd : (f i).data=(g i).data)
    (hh : (f i).skeleton.IsHead ↔ (g i).skeleton.IsHead)
    (hs : (f i).head.side=(g i).head.side) : ∀ h, value f h=value g h := by
  apply same_cuts_fields hf hg hu.cuts
  all_goals
    intro h
    by_cases he : h=i
    · subst h; first | exact hi | exact hd | exact hh | exact fun _ => hs
    · simp only [hu.off h he,implies_true]

lemma unary_create {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) {a : Cell q} {s : Bool}
    (hfi : f i=a.idle s) (hgi : g i=a.boundary s) : ∀ h, value f h=value g h := by
  intro h
  by_cases he : h=i
  · subst h
    rw [idle (by simp [hfi,Cell.idle,Cell.marker]),
      owned hg (h:=i) ⟨Connected.refl _ _,Or.inl (by simp [hgi,Cell.boundary,Skeleton.mark])⟩]
    simp [hfi,hgi,Cell.idle,Cell.boundary,defaultHead]
  · have hic : ¬SameRegion f h i := fun hc => he (hf.idle_component
      (by simp [hfi,Cell.idle,Cell.marker]) hc)
    apply fields hf hg h (fun _ => Connected.congr hu.cuts)
      (by rw [hu.off h he]) (congrArg Cell.data (hu.off h he))
    · intro k hk
      have hki : k≠i := by intro heq; subst k; exact hic hk
      rw [hu.off k hki]
    · intro k hk
      have hki : k≠i := by intro heq; subst k; exact hic hk.1
      rw [hu.off k hki]

lemma unary_nonpivot {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i)
    (hn : ¬ ((f i).marker=.full ∧ (f i).head.phase=.success ∧ (f i).head.side≠(g i).head.side)) :
    ∀ h, value f h=value g h := by
  have he := hu.edge
  generalize hfi : f i=a at he
  generalize hgi : g i=b at he
  cases he with
  | create c s hc => exact unary_create hf hg hu hfi hgi
  | pivot c s hl ht =>
    exfalso
    apply hn
    simp [hfi,hgi,Cell.full,Cell.marker,Skeleton.mark]
  | _ =>
    apply unary_fields hf hg hu <;>
      simp [hfi,hgi,Cell.full,Cell.boundary,Cell.marker,Skeleton.IsHead,Skeleton.mark,defaultHead]

omit [NeZero q] in
lemma moving_head {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hc : ∀ h, cellCut f h ↔ cellCut g h) (hconn : SameRegion f i j)
    (hhi : (f i).skeleton.IsHead) (hhj : (g j).skeleton.IsHead)
    (hoff : ∀ h, h≠i → h≠j → f h=g h)
    (hi : ∀ h, (f h).marker=.idle ↔ (g h).marker=.idle)
    (hd : ∀ h, (f h).data=(g h).data)
    (hs : (f i).head.side=(g j).head.side) : ∀ h, value f h=value g h := by
  intro h
  by_cases ho : SameRegion f h i
  · have ho' : Own g h j := ⟨(Connected.congr hc).mp (ho.trans hconn),hhj⟩
    rw [owned hf ⟨ho,hhi⟩,owned hg ho',hd,hs]
  · have ho' : ¬SameRegion f h j := fun hj => ho (hj.trans hconn.symm)
    apply fields hf hg h (fun _ => Connected.congr hc) (hi h) (hd h)
    · intro k hk
      have hki : k≠i := by intro he; subst k; exact ho hk
      have hkj : k≠j := by intro he; subst k; exact ho' hk
      rw [hoff k hki hkj]
    · intro k hk
      have hki : k≠i := by intro he; subst k; exact ho hk.1
      have hkj : k≠j := by intro he; subst k; exact ho' hk.1
      rw [hoff k hki hkj]

lemma binary_acquire {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool}
    (hfi : f i=a.boundary s) (hfj : f j=b.idle s)
    (hgi : g i=a.wing .left) (hgj : g j=b.boundary s) : ∀ h, value f h=value g h := by
  have hc : ∀ h, h≠i → (cellCut f h ↔ cellCut g h) := hb.cuts_off (by
    simp [cellCut,hfj,hgj,Cell.idle,Cell.boundary,Skeleton.rightExternal,Skeleton.mark])
  have hncut : ¬cellCut g i := by simp [cellCut,hgi,Cell.wing,Skeleton.rightExternal]
  have hmono : ∀ h, cellCut g h → cellCut f h := by
    intro h hh
    by_cases he : h=i
    · subst h; exact (hncut hh).elim
    · exact (hc h he).mpr hh
  have hjoin : SameRegion g i j := (Connected.adjacent_iff hb.adjacent).mpr hncut
  have hihead : (f i).skeleton.IsHead := Or.inl (by simp [hfi,Cell.boundary,Skeleton.mark])
  have hjhead : (g j).skeleton.IsHead := Or.inl (by simp [hgj,Cell.boundary,Skeleton.mark])
  intro h
  by_cases he : h=j
  · subst h
    rw [idle (by simp [hfj,Cell.idle,Cell.marker]),owned hg ⟨Connected.refl _ _,hjhead⟩]
    simp [hfj,hgj,Cell.idle,Cell.boundary,defaultHead]
  · by_cases ho : SameRegion f h i
    · have ho' : SameRegion g h j := (ho.mono hmono).trans hjoin
      rw [owned hf ⟨ho,hihead⟩,owned hg ⟨ho',hjhead⟩]
      have hd : (f h).data=(g h).data := by
        by_cases he' : h=i
        · subst h; simp [hfi,hgi,Cell.boundary,Cell.wing]
        · rw [hb.off h he' he]
      simp only [hfi,hgj,Cell.boundary,hd]
    · have hoj : ¬SameRegion f h j := fun hh => he (hf.idle_component
        (by simp [hfj,Cell.idle,Cell.marker]) hh)
      have hc' (k : Fin N) : SameRegion f h k ↔ SameRegion g h k :=
        Connected.edit_unrelated hb.adjacent hc ho hoj
      have hni : h≠i := by intro hh; subst h; exact ho (Connected.refl _ _)
      apply fields hf hg h hc' (by rw [hb.off h hni he]) (congrArg Cell.data (hb.off h hni he))
      · intro k hk
        have hki : k≠i := by intro hh; subst k; exact ho hk
        have hkj : k≠j := by intro hh; subst k; exact hoj hk
        rw [hb.off k hki hkj]
      · intro k hk
        have hki : k≠i := by intro hh; subst k; exact ho hk.1
        have hkj : k≠j := by intro hh; subst k; exact hoj hk.1
        rw [hb.off k hki hkj]

lemma binary_fields {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j)
    (hci : cellCut f i ↔ cellCut g i) (hcj : cellCut f j ↔ cellCut g j)
    (hmi : (f i).marker=.idle ↔ (g i).marker=.idle) (hmj : (f j).marker=.idle ↔ (g j).marker=.idle)
    (hdi : (f i).data=(g i).data) (hdj : (f j).data=(g j).data)
    (hhi : (f i).skeleton.IsHead ↔ (g i).skeleton.IsHead)
    (hhj : (f j).skeleton.IsHead ↔ (g j).skeleton.IsHead)
    (hsi : (f i).head.side=(g i).head.side) (hsj : (f j).head.side=(g j).head.side) :
    ∀ h, value f h=value g h := by
  apply same_cuts_fields hf hg (hb.cuts hci hcj)
  · exact hb.everywhere (P:=fun a b => a.marker=.idle ↔ b.marker=.idle) (fun _ => Iff.rfl) hmi hmj
  · exact hb.everywhere (P:=fun a b => a.data=b.data) (fun _ => rfl) hdi hdj
  · exact hb.everywhere (P:=fun a b => a.skeleton.IsHead ↔ b.skeleton.IsHead) (fun _ => Iff.rfl) hhi hhj
  · intro h _; exact hb.everywhere (P:=fun a b => a.head.side=b.head.side) (fun _ => rfl) hsi hsj h

theorem binary {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) : ∀ h, value f h=value g h := by
  have he := hb.edge
  generalize hfi : f i=a at he
  generalize hfj : f j=b at he
  generalize hgi : g i=a' at he
  generalize hgj : g j=b' at he
  cases he with
  | acquire a b s hp => exact binary_acquire hf hg hb hfi hfj hgi hgj
  | read_left a b s c r hp | undo_left a b s c r hp =>
    have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
      (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
      (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
    have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
      simp [cellCut,hfi,Cell.wing,Skeleton.rightExternal])
    apply moving_head hf hg hc hconn.symm
      (by simp [hfj,Cell.full,Skeleton.IsHead]) (by simp [hgi,Cell.full,Skeleton.IsHead])
      (fun h hi hj => hb.off h hj hi)
    · apply hb.everywhere (P:=fun a b => a.marker=.idle ↔ b.marker=.idle) (fun _ => Iff.rfl) <;>
        simp [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark]
    · apply hb.everywhere (P:=fun a b => a.data=b.data) (fun _ => rfl) <;> simp [hfi,hfj,hgi,hgj,Cell.wing,Cell.full]
    · simp [hfj,hgi,Cell.full]
  | read_right a b s c r hp | undo_right a b s c r hp =>
    have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
      (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
      (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
    have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
      simp [cellCut,hfi,Cell.full,Skeleton.rightExternal,full_conditions hp])
    apply moving_head hf hg hc hconn
      (by simp [hfi,Cell.full,Skeleton.IsHead]) (by simp [hgj,Cell.full,Skeleton.IsHead]) hb.off
    · apply hb.everywhere (P:=fun a b => a.marker=.idle ↔ b.marker=.idle) (fun _ => Iff.rfl) <;>
        simp [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark]
    · apply hb.everywhere (P:=fun a b => a.data=b.data) (fun _ => rfl) <;> simp [hfi,hfj,hgi,hgj,Cell.wing,Cell.full]
    · simp [hfi,hgj,Cell.full]
  | checker_create a b p x ha hp hb' =>
    apply binary_fields hf hg hb <;>
      simp [hfi,hfj,hgi,hgj,cellCut,Cell.setChecker,Cell.marker]
  | checker_advance a b v x ha hb' hv =>
    apply binary_fields hf hg hb <;>
      simp [hfi,hfj,hgi,hgj,cellCut,Cell.setChecker,Cell.marker]
  | swap a b x y ha hb' hab hna hnb =>
    change a.skeleton.pos=.palette x at ha
    apply binary_fields hf hg hb <;>
      simp [cellCut,hfi,hfj,hgi,hgj,←hab,Cell.setColor,Skeleton.rightExternal,Skeleton.last,
        Skeleton.IsHead,Cell.marker,ha]

lemma PivotAt.symm {f g : Fin N → Cell q} {i : Fin N} (hp : PivotAt f g i) : PivotAt g f i := by
  obtain ⟨a,s,hf,hg,ho,hl,ht⟩ := hp
  exact ⟨a,!s,hg,by simpa using hf,fun h hh => (ho h hh).symm,hl,ht⟩

lemma PivotAt.unary {S : Schedule q} {f g : Fin N → Cell q} {i : Fin N} (hp : PivotAt f g i) :
    UnaryAt S f g i := by
  obtain ⟨a,s,hf,hg,ho,hl,ht⟩ := hp
  exact ⟨ho,by simpa [hf,hg] using Unary.pivot (S:=S) a s hl ht⟩

lemma pivot {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) {a : Cell q} {s : Bool}
    (hfi : f i=a.full s 0 .success 0) (hgi : g i=a.full (!s) 0 .success 0) :
    (∀ h, SameRegion f h i → value f h=(f h).data s) ∧
    (∀ h, value g h=if SameRegion f h i then (f h).data (!s) else value f h) := by
  classical
  have hh : (f i).skeleton.IsHead := Or.inr (by simp [hfi,Cell.full,Skeleton.mark])
  have hk : (g i).skeleton.IsHead := Or.inr (by simp [hgi,Cell.full,Skeleton.mark])
  constructor
  · intro h ho
    simpa [hfi,Cell.full] using owned hf ⟨ho,hh⟩
  · intro h
    by_cases ho : SameRegion f h i
    · rw [ite_eq_left ho,owned hg ⟨(Connected.congr hu.cuts).mp ho,hk⟩]
      have hd : (g h).data=(f h).data := by
        by_cases he : h=i
        · subst h; simp [hfi,hgi,Cell.full]
        · rw [hu.off h he]
      simp [hgi,Cell.full,hd]
    · rw [ite_eq_right ho]
      symm
      have hni : h≠i := by intro he; subst h; exact ho (Connected.refl _ _)
      apply fields hf hg h (fun _ => Connected.congr hu.cuts)
        (by rw [hu.off h hni]) (congrArg Cell.data (hu.off h hni))
      · intro k hk
        have hki : k≠i := by intro he; subst k; exact ho hk
        rw [hu.off k hki]
      · intro k hk
        have hki : k≠i := by intro he; subst k; exact ho hk.1
        rw [hu.off k hki]

lemma unary_classified {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) : (∀ h, value f h=value g h) ∨ PivotAt f g i := by
  have he := hu.edge
  generalize hfi : f i=a at he
  generalize hgi : g i=b at he
  cases he with
  | pivot c s hl ht => exact Or.inr ⟨c,s,hfi,hgi,hu.off,hl,ht⟩
  | _ => exact Or.inl (unary_nonpivot hf hg hu (by
      simp [hfi,hgi,Cell.full,Cell.boundary,Cell.idle,Cell.marker,Skeleton.mark]))

lemma unaryAt_context {S : Schedule q} {f g : Fin N → Cell q} {p s : List (Cell q)} {a b : Cell q}
    (hfv : List.ofFn f=p++[a]++s) (hgv : List.ofFn g=p++[b]++s) (he : Unary S a b) :
    ∃ i, UnaryAt S f g i := by
  have hn := congrArg List.length hfv
  simp only [List.length_ofFn,List.length_append,List.length_singleton] at hn
  let i : Fin N := ⟨p.length,by omega⟩
  have hfi : f i=a := by simpa using Verification.get_of_context hfv i 0 (by simp) (by simp [i])
  have hgi : g i=b := by simpa using Verification.get_of_context hgv i 0 (by simp) (by simp [i])
  refine ⟨i,?_,by simpa [hfi,hgi] using he⟩
  intro h hne
  apply Verification.off_of_context hfv hgv rfl h
  have hn : h.val≠p.length := fun hh => hne (Fin.ext hh)
  simp only [List.length_singleton]
  omega

lemma binaryAt_context {S : Schedule q} {f g : Fin N → Cell q} {p s : List (Cell q)} {a b a' b' : Cell q}
    (hfv : List.ofFn f=p++[a,b]++s) (hgv : List.ofFn g=p++[a',b']++s)
    (he : Binary S a b a' b') : ∃ i j, BinaryAt S f g i j := by
  have hn := congrArg List.length hfv
  simp only [List.length_ofFn,List.length_append,List.length_cons,List.length_nil] at hn
  let i : Fin N := ⟨p.length,by omega⟩
  let j : Fin N := ⟨p.length+1,by omega⟩
  have hfi : f i=a := by simpa using Verification.get_of_context hfv i 0 (by simp) (by simp [i])
  have hfj : f j=b := by simpa using Verification.get_of_context hfv j 1 (by simp) (by simp [j])
  have hgi : g i=a' := by simpa using Verification.get_of_context hgv i 0 (by simp) (by simp [i])
  have hgj : g j=b' := by simpa using Verification.get_of_context hgv j 1 (by simp) (by simp [j])
  refine ⟨i,j,rfl,?_,by simpa [hfi,hfj,hgi,hgj] using he⟩
  intro h hne hne'
  apply Verification.off_of_context hfv hgv rfl h
  have hni : h.val≠p.length := fun hh => hne (Fin.ext hh)
  have hnj : h.val≠p.length+1 := fun hh => hne' (Fin.ext hh)
  simp only [List.length_cons,List.length_nil]
  omega

theorem step_classified {S : Schedule q} {f g : Fin N → Cell q} {d : ℕ}
    (hf : Syntax S d (List.ofFn f)) (he : Step S d (List.ofFn f) (List.ofFn g)) :
    (∀ h, value f h=value g h) ∨ ∃ i, PivotAt f g i := by
  have hg := reach_syntax (Relation.ReflTransGen.single he) hf
  have hf' := Verification.coherent_of_syntax S hf
  have hg' := Verification.coherent_of_syntax S hg
  obtain ⟨p,s,v,w,hf,hg,hh⟩ := he
  rcases hh.2 with ⟨a,b,rfl,rfl,he⟩ | ⟨a,b,a',b',rfl,rfl,he⟩
  · rcases he with he | he
    · obtain ⟨i,hi⟩ := unaryAt_context hf hg he
      exact (unary_classified hf' hg' hi).imp id (fun hh => ⟨i,hh⟩)
    · obtain ⟨i,hi⟩ := unaryAt_context hg hf he
      exact (unary_classified hg' hf' hi).imp (fun hh h => (hh h).symm) (fun hh => ⟨i,hh.symm⟩)
  · rcases he with he | he
    · obtain ⟨i,j,hb⟩ := binaryAt_context hf hg he
      exact Or.inl (binary hf' hg' hb)
    · obtain ⟨i,j,hb⟩ := binaryAt_context hg hf he
      exact Or.inl (fun h => (binary hg' hf' hb h).symm)

end Committed

namespace Verification
variable (S : Schedule q)

omit [NeZero q] in
lemma good_success {f : Fin N → Cell q} {i : Fin N} (hi : Good S f i)
    (hp : (f i).head.phase=.success) :
    (f i).head.reg=0 ∧ ∀ j : Fin q, j.val < (S.count (f i).metadata.task).val → holds S f i j := by
  simpa [Good,hp,potential] using hi

omit [NeZero q] in
lemma good_semanticZero_sound {f : Fin N → Cell q} {i : Fin N} (hi : Good S f i)
    (hz : SemanticZero S (f i)) :
    (f i).head.phase=.success ∧ (f i).metadata.zeroTask=true ∧ (f i).head.reg=0 ∧
      ∀ j : Fin q, j.val < (S.count (f i).metadata.task).val → holds S f i j := by
  have hh := good_semanticZero S hi hz
  exact ⟨hh.1,hh.2,(good_success S hi hh.1).1,(good_success S hi hh.1).2⟩

end Verification
end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordComponents
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instTransCellGeomRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]

namespace Component
variable (f : Fin N → Cell q) (i : Fin N)

omit [NeZero q] in
lemma offset_injective : Function.Injective (offset f i) := by
  intro a b hab
  apply Fin.ext
  have hh := congrArg Fin.val hab
  dsimp [offset] at hh
  omega

omit [NeZero q] in
lemma sum_offset {A : Type*} [AddCommMonoid A] (a : Fin N → A) :
    (∑ k : Fin (size f i), a (offset f i k)) = ∑ j ∈ members f i, a j := by
  classical
  apply Finset.sum_bij (fun k _ => offset f i k)
  · intro k hk
    exact (mem_iff f i _).mpr (connected_offset f i k)
  · intro a ha b hb hh
    exact offset_injective f i hh
  · intro j hj
    obtain ⟨k,hk⟩ := offset_surjective f i ((mem_iff f i j).mp hj)
    exact ⟨k,Finset.mem_univ _,hk⟩
  · intro k hk; rfl

lemma total_region {S : Schedule q} {d : ℕ} (hs : Syntax S d (List.ofFn f))
    (hi : (f i).marker=.full) (j : Fin (S.count (region f i hs hi).task).val) :
    (((region f i hs hi).plan S).payload j).total =
      Verification.total S f i ((region f i hs hi).clauseIndex S j) := by
  classical
  change (∑ k : Fin (size f i), (f (offset f i k)).delta
      (S.clause (f i).metadata.task ((region f i hs hi).clauseIndex S j))) = _
  rw [sum_offset f i (fun k => (f k).delta (S.clause (f i).metadata.task
    ((region f i hs hi).clauseIndex S j)))]
  simp [members,Finset.sum_filter,Verification.total,Verification.sum]

lemma region_holds {S : Schedule q} {d : ℕ} (hs : Syntax S d (List.ofFn f))
    (hi : (f i).marker=.full) (hg : Verification.Good S f i)
    (hp : (f i).head.phase=.success) : ∀ j, ((region f i hs hi).plan S).Holds j := by
  intro j
  have ht := (Verification.good_success S hg hp).2
  change (S.clause (f i).metadata.task ((region f i hs hi).clauseIndex S j)).truth _=true
  rw [total_region f i hs hi j]
  exact ht _ j.isLt

end Component

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordRewriting
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instTransCellGeomRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

lemma canonicalBlock_format (bits : Fin d → ZMod 2) :
    ∀ c ∈ canonicalBlock (q:=q) bits, c.Format S d := by
  intro c hc
  simp only [canonicalBlock,List.mem_append,List.mem_map,List.mem_singleton] at hc
  rcases hc with (⟨p,_,rfl⟩|⟨x,_,rfl⟩)|rfl <;> exact canonicalCell_format _ _

omit [NeZero q] in
lemma closed_of_pair_chain (w : List (Skeleton q 10))
    (ha : ∀ c ∈ w, c.Admissible) (hc : w.IsChain Skeleton.Pair)
    (hl : ∀ c ∈ w.head?, c.leftExternal) (hr : ∀ c ∈ w.getLast?, c.rightExternal) :
    Skeleton.Closed w := by
  refine ⟨ha,?_⟩
  have hm : (w.map some).IsChain Skeleton.Link := by
    simpa only [List.isChain_map,Skeleton.Link] using hc
  have ht : (w.map some ++ [none]).IsChain Skeleton.Link := by
    apply hm.append (List.isChain_singleton _)
    intro a hea b heb
    simp only [List.head?_cons,Option.mem_def,Option.some.injEq] at heb
    subst b
    cases he : w.getLast? with
    | none => simp [List.getLast?_map,he] at hea
    | some c =>
      simp only [List.getLast?_map,he,Option.map_some,Option.mem_def,Option.some.injEq] at hea
      subst a
      exact hr c (by simp [he])
  apply ht.cons
  intro a hea
  cases w with
  | nil =>
    simp only [List.map_nil,List.nil_append,List.head?_cons, Option.mem_def,Option.some.injEq] at hea
    subst a
    trivial
  | cons c w =>
    simp only [List.map_cons,List.cons_append,List.head?_cons,Option.mem_def,Option.some.injEq] at hea
    subst a
    exact hl c (by simp)

lemma encodeWord_syntax (w : List (Fin d → ZMod 2)) :
    Syntax S d (encodeWord (q:=q) w) := by
  have hf : ∀ c ∈ encodeWord (q:=q) w, c.Format S d := by
    intro c hc
    obtain ⟨b,hb,hc⟩ := List.mem_flatMap.mp hc
    exact canonicalBlock_format b c hc
  have hi : ∀ c ∈ encodeWord (q:=q) w, c.marker=.idle := by
    intro c hc
    obtain ⟨b,hb,hc⟩ := List.mem_flatMap.mp hc
    simp only [canonicalBlock,List.mem_append,List.mem_map,List.mem_singleton] at hc
    rcases hc with (⟨p,_,rfl⟩|⟨x,_,rfl⟩)|rfl <;> rfl
  have hchain := encodeWord_pair_chain (q:=q) w
  refine ⟨?_,hchain.imp (fun _ _ h => h.2),hf⟩
  apply closed_of_pair_chain
  · intro s hs
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs
    exact (hf c hc).1
  · simpa only [List.isChain_map] using hchain.imp (fun _ _ h => h.1)
  · intro s hs
    have hs' := List.mem_of_mem_head? hs
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs'
    exact Or.inl (hi c hc)
  · intro s hs
    have hs' := List.mem_of_mem_getLast? hs
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs'
    exact Or.inl (hi c hc)

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_GeometricRelations
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable

open LocalSyntax LocalSyntax.Skeleton
namespace Rigid
variable {q d n : ℕ} [NeZero q]

omit [NeZero q] in
lemma cell_block_coord (i : Fin (n*width q)) : cell (block i) (coord i)=i := by
  apply Fin.ext
  simpa [cell,block,coord,Nat.mul_comm] using Nat.div_add_mod i.val (width q)

omit [NeZero q] in
lemma shape_core_iff (i : Fin (width q)) (p : Fin q) :
    shape i=.core p ↔ i.val=p.val := by
  rw [←position_core_iff]
  cases hp : position i <;> simp [shape,hp]

lemma layout_encoded (u : Fin n → Fin d → ZMod 2) : Layout (encoded (q:=q) u) := by
  intro i
  unfold encoded Cell.shape shape
  rw [canonicalCell_pos]
  rfl

omit [NeZero q] in
lemma decoded_eq {hd : d≤q} {f g : Fin (n*width q) → Cell q}
    (h : ∀i,Committed.value f i=Committed.value g i) : decoded hd f=decoded hd g := by
  funext b p
  exact h _

lemma decoded_encoded (hd : d≤q) (u : Fin n → Fin d → ZMod 2) :
    decoded hd (encoded (q:=q) u)=u := by
  funext b p
  rw [decoded,Committed.idle (by simp [encoded])]
  rw [core,encoded_cell]
  have hp : position (⟨(p.castLE hd).val,by have := (p.castLE hd).isLt; simp [width]; omega⟩ :
      Fin (width q))=.core (p.castLE hd) := (position_core_iff _ _).mpr rfl
  rw [hp]
  simp [canonicalCell,p.isLt]

omit [NeZero q] in
lemma layout_core {f : Fin (n*width q) → Cell q} (hf : Layout f) (b : Fin n) (p : Fin q) :
    (f (core b p)).pos=.core p := by
  apply (Cell.shape_core_iff _ _).mp
  rw [hf,core,coord_cell]
  exact (shape_core_iff _ _).mpr rfl
omit [NeZero q] in
lemma layout_core_iff {f : Fin (n*width q) → Cell q} (hf : Layout f)
    (i : Fin (n*width q)) (p : Fin q) :
    (f i).pos=.core p ↔ i.val%width q=p.val := by
  rw [←Cell.shape_core_iff,hf,shape_core_iff]
  rfl

lemma layout_reach {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hf : Layout f) (hr : Reach S d (List.ofFn f) (List.ofFn g)) : Layout g := by
  have he := reach_shape hr
  simp only [List.map_ofFn] at he
  have he' := List.ofFn_injective he
  intro i
  exact (congrFun he' i).symm.trans (hf i)

omit [NeZero q] in
lemma block_mono {i j : Fin (n*width q)} (h : i≤j) : block i≤block j :=
  Nat.div_le_div_right h

omit [NeZero q] in
lemma first_le_iff (b : Fin n) (j : Fin (n*width q)) :
    cell b ⟨0,width_pos⟩≤j ↔ b≤block j := by
  constructor
  · intro h
    simpa only [block_cell] using block_mono h
  · intro h
    have hm := Nat.mul_le_mul_right (width q) h
    have he := congrArg Fin.val (cell_block_coord j)
    change b.val*width q+0≤j.val
    change (block j).val*width q+(coord j).val=j.val at he
    omega
omit [NeZero q] in
lemma le_last_iff (b : Fin n) (j : Fin (n*width q)) :
    j ≤ cell b ⟨2*q,by simp [width]⟩ ↔ block j≤b := by
  constructor
  · intro h
    simpa only [block_cell] using block_mono h
  · intro h
    have hm := Nat.mul_le_mul_right (width q) h
    have he := congrArg Fin.val (cell_block_coord j)
    change j.val≤b.val*width q+2*q
    change (block j).val*width q+(coord j).val=j.val at he
    have hp : (coord j).val≤2*q := by have := (coord j).isLt; unfold width at this; omega
    omega

section Component
variable {S : Schedule q} {f : Fin (n*width q) → Cell q} (hl : Layout f)
  (hs : Syntax S d (List.ofFn f)) (i : Fin (n*width q)) (hi : (f i).marker=.full)
include hl hs hi

lemma component_left_mod : (Component.left f i).val%width q=0 := by
  obtain ⟨_,p,hp,hz⟩ := Component.first f i (Verification.coherent_of_syntax S hs)
    (exterior_of_syntax hs) (Or.inr hi)
  change (f (Component.left f i)).pos=.core p at hp
  rw [layout_core_iff hl _ _] at hp
  omega
lemma component_right_mod : (Component.right f i).val%width q=2*q := by
  exact (layout_stop_iff hl _).mp (Component.last f i (Verification.coherent_of_syntax S hs)
    (exterior_of_syntax hs) hi).2

lemma component_left_cell : Component.left f i=cell (block (Component.left f i)) ⟨0,width_pos⟩ := by
  have hh := cell_block_coord (Component.left f i)
  have hc : coord (Component.left f i)=⟨0,width_pos⟩ := Fin.ext (component_left_mod hl hs i hi)
  rw [hc] at hh
  exact hh.symm
lemma component_right_cell : Component.right f i=cell (block (Component.right f i))
    ⟨2*q,by simp [width]⟩ := by
  have hh := cell_block_coord (Component.right f i)
  have hc : coord (Component.right f i)=⟨2*q,by simp [width]⟩ :=
    Fin.ext (component_right_mod hl hs i hi)
  rw [hc] at hh
  exact hh.symm

lemma component_interval (j : Fin (n*width q)) : SameRegion f i j ↔
    (block (Component.left f i)).val≤(block j).val ∧
      (block j).val<(block (Component.left f i)).val+(f i).metadata.arity.val+1 := by
  rw [Component.interval,component_left_cell hl hs i hi,component_right_cell hl hs i hi,
    first_le_iff,le_last_iff]
  change (block (Component.left f i)).val≤(block j).val ∧
    (block j).val≤(block (Component.right f i)).val ↔ _
  rw [component_last_block hl hs i hi]
  simp only [block_cell]
  omega

lemma regionCore_owned (b : Fin ((f i).metadata.arity.val+1)) (p : Fin q) :
    SameRegion f i (core (regionBlock hl hs i hi b) p) := by
  rw [component_interval hl hs i hi]
  simp only [core,block_cell,regionBlock]
  have := b.isLt
  omega

lemma region_cell (b : Fin ((f i).metadata.arity.val+1)) (p : Fin q) :
    let R := Component.region f i hs hi
    R.cell (R.locate b p)=f (core (regionBlock hl hs i hi b) p) := by
  intro R
  obtain ⟨j,hj⟩ := Component.offset_surjective f i (regionCore_owned hl hs i hi b p)
  have hc : (R.cell j).pos=.core p := by
    change (f (Component.offset f i j)).pos=.core p
    rw [hj]
    exact layout_core hl _ _
  have hb : (R.cell j).metadata.block.val=b.val := by
    have hh := component_block_counter hl hs i hi j
    rw [hj] at hh
    rw [show block (core (regionBlock hl hs i hi b) p)=regionBlock hl hs i hi b from block_cell _ _] at hh
    change (f (core (regionBlock hl hs i hi b) p)).metadata.block.val+
      (block (Component.left f i)).val=(block (Component.left f i)).val+b.val at hh
    change (f (Component.offset f i j)).metadata.block.val=b.val
    rw [hj]
    omega
  have he := R.locate_unique b p j hb hc
  rw [←he]
  exact congrArg f hj

end Component

lemma split_ofFn {α : Type*} (f : Fin n → α) (a k : ℕ) (h : a+k≤n) :
    List.ofFn f =
      List.ofFn (fun i : Fin a => f ⟨i.val,by have := i.isLt; omega⟩) ++
      List.ofFn (fun i : Fin k => f ⟨a+i.val,by have := i.isLt; omega⟩) ++
      List.ofFn (fun i : Fin (n-(a+k)) => f ⟨a+k+i.val,by have := i.isLt; omega⟩) := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    simp only [List.length_append,List.length_ofFn,List.getElem_append,List.getElem_ofFn]
    split_ifs <;> apply congrArg f <;> apply Fin.ext <;> dsimp only <;> omega

lemma context_of_interval {α : Type*} (f g : Fin n → α) (a k : ℕ) (h : a+k≤n)
    (u v : Fin k → α)
    (hu : ∀ i : Fin k, f ⟨a+i.val,by have := i.isLt; omega⟩=u i)
    (hv : ∀ i : Fin k, g ⟨a+i.val,by have := i.isLt; omega⟩=v i)
    (ho : ∀ i : Fin n, ¬(a ≤ i.val ∧ i.val < a+k) → f i=g i) :
    ∃ p s : List α, List.ofFn f=p++List.ofFn u++s ∧ List.ofFn g=p++List.ofFn v++s := by
  refine ⟨List.ofFn (fun i : Fin a => f ⟨i.val,by have := i.isLt; omega⟩),
    List.ofFn (fun i : Fin (n-(a+k)) => f ⟨a+k+i.val,by have := i.isLt; omega⟩),?_,?_⟩
  · rw [split_ofFn f a k h]
    simp only [hu]
  · rw [split_ofFn g a k h]
    simp only [hv]
    congr 2
    · apply congrArg List.ofFn
      funext i
      symm
      apply ho
      have := i.isLt
      dsimp only
      omega
    · funext i
      symm
      apply ho
      dsimp only
      omega

theorem pivot_context {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hd : d≤q) (hl : Layout f) (hs : Syntax S d (List.ofFn f))
    (ht : Syntax S d (List.ofFn g)) {i : Fin (n*width q)} (hp : Committed.PivotAt f g i) :
    ∃ (hi : (f i).marker=.full) (s : Bool) (p t : List (Fin d → ZMod 2)),
      let R := Component.region f i hs hi
      (f i).metadata.zeroTask=false ∧ (f i).head.phase=.success ∧
      List.ofFn (decoded hd f)=p++List.ofFn (fun b p => R.slot s b (p.castLE hd))++t ∧
      List.ofFn (decoded hd g)=p++List.ofFn (fun b p => R.slot (!s) b (p.castLE hd))++t := by
  obtain ⟨a,s,hfi,hgi,hoff,hlast,hzero⟩ := hp
  have hi : (f i).marker=.full := by simp [hfi,Cell.full,Cell.marker,Skeleton.mark]
  let R := Component.region f i hs hi
  have hp : Committed.PivotAt f g i := ⟨a,s,hfi,hgi,hoff,hlast,hzero⟩
  have hv := Committed.pivot (Verification.coherent_of_syntax S hs)
    (Verification.coherent_of_syntax S ht) (hp.unary (S:=S)) hfi hgi
  have hfslot (b : Fin ((f i).metadata.arity.val+1)) (p : Fin d) :
      decoded hd f (regionBlock hl hs i hi b) p=R.slot s b (p.castLE hd) := by
    rw [decoded,hv.1 _ (Connected.symm (regionCore_owned hl hs i hi b (p.castLE hd)))]
    change _ = (R.cell (R.locate b (p.castLE hd))).data _
    rw [region_cell hl hs i hi]
  have hgslot (b : Fin ((f i).metadata.arity.val+1)) (p : Fin d) :
      decoded hd g (regionBlock hl hs i hi b) p=R.slot (!s) b (p.castLE hd) := by
    rw [decoded,hv.2,ite_eq_left (Connected.symm (regionCore_owned hl hs i hi b (p.castLE hd)))]
    change _ = (R.cell (R.locate b (p.castLE hd))).data _
    rw [region_cell hl hs i hi]
  have hb : (block (Component.left f i)).val+((f i).metadata.arity.val+1)≤n := by
    have hh := component_last_block hl hs i hi
    have hr := (block (Component.right f i)).isLt
    omega
  obtain ⟨p,t,hf,hg⟩ := context_of_interval (decoded hd f) (decoded hd g)
    (block (Component.left f i)).val ((f i).metadata.arity.val+1) hb
    (fun b p => R.slot s b (p.castLE hd)) (fun b p => R.slot (!s) b (p.castLE hd))
    (fun b => funext (hfslot b)) (fun b => funext (hgslot b)) (by
      intro b hbo
      funext p
      rw [decoded,decoded,hv.2,ite_eq_right]
      intro ho
      have hh := (component_interval hl hs i hi (core b (p.castLE hd))).mp ho.symm
      simp only [core,block_cell] at hh
      exact hbo (by simpa [Nat.add_assoc] using hh))
  refine ⟨hi,s,p,t,?_,?_,hf,hg⟩
  · simpa [hfi,Cell.full,Cell.metadata,Skeleton.mark] using hzero
  · simp [hfi,Cell.full]

end Rigid
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_DataWords
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
section
open LocalSyntax LocalSyntax.Skeleton
variable {q d n : ℕ} [NeZero q]

namespace Rigid
lemma decoded_step {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hd : d≤q) (hl : Layout f) (hs : Syntax S d (List.ofFn f))
    (hg : Verification.AllGood S f) (he : Step S d (List.ofFn f) (List.ofFn g)) :
    CheckedReach S hd (List.ofFn (decoded hd f)) (List.ofFn (decoded hd g)) := by
  obtain hz|⟨i,hp⟩ := Committed.step_classified hs he
  · rw [decoded_eq hz]
    exact .refl
  · have ht := reach_syntax (Relation.ReflTransGen.single he) hs
    obtain ⟨hi,s,p,t,hzero,hphase,hf,hg'⟩ := pivot_context hd hl hs ht hp
    have hc := Component.region_holds f i hs hi (hg i hi) hphase
    rw [hf,hg']
    exact .single (.mk (Component.region f i hs hi) s hzero hc p t)

theorem decoded_reach {S : Schedule q} (hd : d≤q) {f g : Fin (n*width q) → Cell q}
    (hl : Layout f) (hs : Syntax S d (List.ofFn f)) (hg : Verification.AllGood S f)
    (hr : Reach S d (List.ofFn f) (List.ofFn g)) :
    CheckedReach S hd (List.ofFn (decoded hd f)) (List.ofFn (decoded hd g)) := by
  generalize he : List.ofFn g=w at hr
  induction hr generalizing g with
  | refl =>
    have hfg : f=g := List.ofFn_injective he.symm
    subst g
    exact .refl
  | @tail v w h e ih =>
    have hvlen : v.length=n*width q := by
      have hh := reach_length h
      simpa using hh.symm
    let mid : Fin (n*width q) → Cell q := fun i => v.get (Fin.cast hvlen.symm i)
    have hm : List.ofFn mid=v := by
      rw [show mid=(fun i => v.get (Fin.cast hvlen.symm i)) from rfl,
        ←List.ofFn_congr hvlen v.get]
      exact List.ofFn_get v
    have hmreach : Reach S d (List.ofFn f) (List.ofFn mid) := by rwa [hm]
    have hmstep : Step S d (List.ofFn mid) (List.ofFn g) := by rwa [hm,he]
    have hmgood : Verification.AllGood S mid := by
      have hh := (Verification.wordGood_reach S hs hmreach).mp
        ((Verification.wordGood_ofFn S f).mpr hg)
      exact (Verification.wordGood_ofFn S mid).mp hh
    exact (ih (g:=mid) hm).trans (decoded_step hd (layout_reach hl hmreach)
      (reach_syntax hmreach hs) hmgood hmstep)

lemma encoded_idle (u : Fin n → Fin d → ZMod 2) (i : Fin (n*width q)) :
    (encoded u i).marker=.idle := rfl

theorem clean_decoded_reach {S : Schedule q} (hd : d≤q) (u : Fin n → Fin d → ZMod 2)
    (g : Fin (n*width q) → Cell q)
    (hr : Reach S d (encodeWord (List.ofFn u)) (List.ofFn g)) :
    CheckedReach S hd (List.ofFn u) (List.ofFn (decoded hd g)) := by
  have hf : Syntax S d (List.ofFn (encoded (q:=q) u)) := by
    rw [encoded_ofFn]
    exact encodeWord_syntax _
  have hg : Verification.AllGood S (encoded (q:=q) u) :=
    Verification.allGood_of_idle S (encoded u) (encoded_idle u)
  rw [←encoded_ofFn] at hr
  simpa [decoded_encoded] using decoded_reach hd (layout_encoded u) hf hg hr

lemma component_context {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hd : d≤q) (hl : Layout f) (hs : Syntax S d (List.ofFn f))
    (i : Fin (n*width q)) (hi : (f i).marker=.full) :
    ∃ p t : List (Fin d → ZMod 2),
      List.ofFn (decoded hd f)=p++(Component.region f i hs hi).dataWord hd (f i).head.side++t := by
  let R := Component.region f i hs hi
  have hv (b : Fin ((f i).metadata.arity.val+1)) (p : Fin d) :
      decoded hd f (regionBlock hl hs i hi b) p=R.slot (f i).head.side b (p.castLE hd) := by
    rw [decoded,Committed.owned (Verification.coherent_of_syntax S hs)
      ⟨(regionCore_owned hl hs i hi b (p.castLE hd)).symm,Or.inr hi⟩]
    change _ = (R.cell (R.locate b (p.castLE hd))).data _
    rw [region_cell hl hs i hi]
  have hb : (block (Component.left f i)).val+((f i).metadata.arity.val+1)≤n := by
    have hh := component_last_block hl hs i hi
    have hr := (block (Component.right f i)).isLt
    omega
  obtain ⟨p,t,hf,_⟩ := context_of_interval (decoded hd f) (decoded hd f)
    (block (Component.left f i)).val ((f i).metadata.arity.val+1) hb
    (fun b p => R.slot (f i).head.side b (p.castLE hd))
    (fun b p => R.slot (f i).head.side b (p.castLE hd))
    (fun b => funext (hv b)) (fun b => funext (hv b)) (fun _ _ => rfl)
  exact ⟨p,t,hf⟩

theorem semanticZero_checked {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hd : d≤q) (hl : Layout f) (hs : Syntax S d (List.ofFn f))
    (hg : Verification.AllGood S f) (i : Fin (n*width q)) (hz : SemanticZero S (f i)) :
    CheckedZero S hd (List.ofFn (decoded hd f)) := by
  have hi : (f i).marker=.full := hz.1
  have hh := Verification.good_semanticZero_sound S (hg i hi) hz
  have hfmt := hs.2.2 (f i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hs0 : (f i).head.side=false := hfmt.2.2.2.2.2.2.2.1 (Or.inr hi) hh.2.1
  obtain ⟨p,t,hp⟩ := component_context hd hl hs i hi
  refine ⟨Component.region f i hs hi,p,t,hh.2.1,
    Component.region_holds f i hs hi (hg i hi) hh.1,?_⟩
  simpa [hs0] using hp

end Rigid
end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Cell
omit [NeZero q] in
lemma checkerSafe_idle (c : Cell q) (hc : c.checker=.idle) : c.CheckerSafe := by
  intro x hx
  simp [hc]
end Cell

lemma unary_checkerSafe {S : Schedule q} {a b : Cell q} (hu : Unary S a b) :
    a.CheckerSafe ↔ b.CheckerSafe := by cases hu <;> exact Iff.rfl

lemma binary_checkerSafe {S : Schedule q} {a b a' b' : Cell q} (hu : Binary S a b a' b') :
    (a.CheckerSafe ∧ b.CheckerSafe) ↔ (a'.CheckerSafe ∧ b'.CheckerSafe) := by
  cases hu with
  | acquire => exact Iff.rfl
  | read_left => exact Iff.rfl
  | read_right => exact Iff.rfl
  | undo_left => exact Iff.rfl
  | undo_right => exact Iff.rfl
  | checker_create a b p x ha hp hb =>
    simp [Cell.CheckerSafe,Cell.setChecker]
  | checker_advance a b v x ha hb hv =>
    change a.skeleton.pos=.palette v at ha
    simp [Cell.CheckerSafe,Cell.setChecker,Cell.pos,ha,Ne.symm hv]
  | swap => exact and_comm

lemma checkerSafe_step {S : Schedule q} {v w : List (Cell q)} (he : Step S d v w) :
    (∀c∈v,c.CheckerSafe) ↔ (∀c∈w,c.CheckerSafe) := by
  obtain ⟨p,s,a,b,rfl,rfl,hh⟩ := he
  have hs : (∀c∈a,c.CheckerSafe) ↔ (∀c∈b,c.CheckerSafe) := by
    rcases hh.2 with ⟨a,b,rfl,rfl,h⟩|⟨a,b,a',b',rfl,rfl,h⟩
    · simpa using h.elim unary_checkerSafe (fun h => (unary_checkerSafe h).symm)
    · simpa using h.elim binary_checkerSafe (fun h => (binary_checkerSafe h).symm)
  simpa only [List.forall_mem_append] using (and_congr (and_congr Iff.rfl hs) Iff.rfl)

lemma checkerSafe_reach {S : Schedule q} {v w : List (Cell q)} (he : Reach S d v w) :
    (∀c∈v,c.CheckerSafe) ↔ (∀c∈w,c.CheckerSafe) := by
  induction he with
  | refl => rfl
  | tail h e ih => exact ih.trans (checkerSafe_step e)

lemma encodeWord_checkerSafe (u : List (Fin d → ZMod 2)) :
    ∀c∈encodeWord (q:=q) u,c.CheckerSafe := by
  intro c hc
  obtain ⟨bits,hb,hc⟩ := List.mem_flatMap.mp hc
  apply Cell.checkerSafe_idle
  simp only [canonicalBlock,List.mem_append,List.mem_map,List.mem_singleton] at hc
  rcases hc with (⟨p,_,rfl⟩|⟨p,_,rfl⟩)|rfl <;> rfl

end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d n : ℕ} [NeZero q]
namespace Cell
lemma color_eq (a : Cell q) (x : Fin q) (h : a.pos=.palette x) : a.color=x := by
  simp [color,h]
end Cell
namespace Rigid

omit [NeZero q] in
lemma palCell_injective (b : Fin n) : Function.Injective (palCell (q:=q) b) := by
  intro x y h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change b.val*width q+(q+x.val)=b.val*width q+(q+y.val) at hh
  omega

lemma palCell_palette {f : Fin (n*width q) → Cell q} (hl : Layout f) (b : Fin n) (p : Fin q) :
    (f (palCell b p)).isPalette := by
  rw [layout_palette_iff hl]
  have hh := congrArg Fin.val (coord_cell b (⟨q+p.val,by have := p.isLt; dsimp [width]; omega⟩ : Fin (width q)))
  change (palCell b p).val%width q=q+p.val at hh
  rw [hh]
  have := p.isLt
  omega

lemma palOffset_cell {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (i : Fin (n*width q)) (hi : (f i).isPalette) :
    palCell (block i) (palOffset hl i hi)=i := by
  have hh := (layout_palette_iff hl i).mp hi
  have he := cell_block_coord i
  apply Fin.ext
  have he' := congrArg Fin.val he
  change (block i).val*width q+(q+(i.val%width q-q))=i.val
  change (block i).val*width q+(i.val%width q)=i.val at he'
  omega

lemma adjacent_palettes_block {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (i j : Fin (n*width q)) (hij : i.val+1=j.val) (hi : (f i).isPalette) :
    block i=block j := by
  have hh := (layout_palette_iff hl i).mp hi
  have hb := block_next hij
  rw [ite_eq_right (by omega),Nat.add_zero] at hb
  exact Fin.ext hb.symm

lemma colors_pos {f g : Fin (n*width q) → Cell q} (h : ∀i,(f i).pos=(g i).pos) (b : Fin n) :
    colors f b=colors g b := by
  apply congrArg List.ofFn
  funext p
  simp only [Cell.color,h]

lemma colors_swap {f g : Fin (n*width q) → Cell q} (hl : Layout f)
    (i j : Fin (n*width q)) (hij : i.val+1=j.val) (hi : (f i).isPalette) (hj : (f j).isPalette)
    (hgi : g i=f j) (hgj : g j=f i) (ho : ∀k,k≠i → k≠j → f k=g k) (b : Fin n) :
    (colors f b).Perm (colors g b) := by
  classical
  have hb := adjacent_palettes_block hl i j hij hi
  by_cases hbi : block i=b
  · let pi := palOffset hl i hi
    let pj := palOffset hl j hj
    have hei : palCell b pi=i := by rw [←hbi]; exact palOffset_cell hl i hi
    have hej : palCell b pj=j := by rw [←hbi,hb]; exact palOffset_cell hl j hj
    have he : (fun p => (g (palCell b p)).color)=
        (fun p => (f (palCell b p)).color) ∘ Equiv.swap pi pj := by
      funext p
      by_cases hp : p=pi
      · subst p
        simp [hei,hej,hgi]
      · by_cases hp' : p=pj
        · subst p
          simp [hei,hej,hgj]
        · rw [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne hp hp']
          rw [←ho]
          · intro h
            exact hp (palCell_injective b (h.trans hei.symm))
          · intro h
            exact hp' (palCell_injective b (h.trans hej.symm))
    unfold colors
    rw [he]
    exact ((Equiv.swap pi pj).ofFn_comp_perm _).symm
  · have hbj : block j≠b := by rwa [←hb]
    have he : colors f b=colors g b := by
      apply congrArg List.ofFn
      funext p
      rw [ho]
      · intro h
        have hh := congrArg block h
        rw [palCell,block_cell] at hh
        exact hbi hh.symm
      · intro h
        have hh := congrArg block h
        rw [palCell,block_cell] at hh
        exact hbj hh.symm
    rw [he]

lemma unary_colors {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    {i : Fin (n*width q)} (hu : UnaryAt S f g i) (b : Fin n) :
    colors f b=colors g b := by
  apply colors_pos
  intro k
  by_cases hk : k=i
  · subst k
    have hh {a c : Cell q} (he : Unary S a c) : a.pos=c.pos := by cases he <;> rfl
    exact hh hu.edge
  · rw [hu.off k hk]

lemma binary_colors {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hl : Layout f) {i j : Fin (n*width q)} (hu : BinaryAt S f g i j) (b : Fin n) :
    (colors f b).Perm (colors g b) := by
  have hh := hu.edge
  generalize hfi : f i=a at hh
  generalize hfj : f j=c at hh
  generalize hgi : g i=a' at hh
  generalize hgj : g j=c' at hh
  cases hh with
  | swap a c x y ha hc he hn hn' =>
    exact colors_swap hl i j hu.adjacent ⟨x,(congrArg Cell.pos hfi).trans ha⟩ ⟨y,(congrArg Cell.pos hfj).trans hc⟩
      (hgi.trans hfj.symm) (hgj.trans hfi.symm) hu.off b
  | _ =>
    apply List.Perm.of_eq
    apply colors_pos
    intro k
    by_cases hk : k=i
    · subst k; rw [hfi,hgi] <;> rfl
    · by_cases hk' : k=j
      · subst k; rw [hfj,hgj]; rfl
      · rw [hu.off k hk hk']

lemma colors_step {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hl : Layout f) (he : Step S d (List.ofFn f) (List.ofFn g)) (b : Fin n) :
    (colors f b).Perm (colors g b) := by
  have hlg := layout_reach hl (Relation.ReflTransGen.single he)
  obtain ⟨p,s,v,w,hf,hg,hr⟩ := he
  rcases hr.2 with ⟨a,c,rfl,rfl,hh⟩|⟨a,c,a',c',rfl,rfl,hh⟩
  · rcases hh with hh|hh
    · obtain ⟨i,hi⟩ := Committed.unaryAt_context hf hg hh
      exact List.Perm.of_eq (unary_colors hi b)
    · obtain ⟨i,hi⟩ := Committed.unaryAt_context hg hf hh
      exact (List.Perm.of_eq (unary_colors hi b)).symm
  · rcases hh with hh|hh
    · obtain ⟨i,j,hij⟩ := Committed.binaryAt_context hf hg hh
      exact binary_colors hl hij b
    · obtain ⟨i,j,hij⟩ := Committed.binaryAt_context hg hf hh
      exact (binary_colors hlg hij b).symm

lemma colors_reach {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hl : Layout f) (hr : Reach S d (List.ofFn f) (List.ofFn g)) (b : Fin n) :
    (colors f b).Perm (colors g b) := by
  generalize he : List.ofFn g=w at hr
  induction hr generalizing g with
  | refl =>
    have hfg : f=g := List.ofFn_injective he.symm
    subst g
    exact .refl _
  | @tail v w h e ih =>
    have hvlen : v.length=n*width q := by have hh := reach_length h; simpa using hh.symm
    let mid : Fin (n*width q) → Cell q := fun i => v.get (Fin.cast hvlen.symm i)
    have hm : List.ofFn mid=v := by
      rw [show mid=(fun i => v.get (Fin.cast hvlen.symm i)) from rfl,
        ←List.ofFn_congr hvlen v.get]
      exact List.ofFn_get v
    have hmreach : Reach S d (List.ofFn f) (List.ofFn mid) := by rwa [hm]
    have hmstep : Step S d (List.ofFn mid) (List.ofFn g) := by rwa [hm,he]
    exact (ih (g:=mid) hm).trans (colors_step (layout_reach hl hmreach) hmstep b)

omit [NeZero q] in
lemma pal_position (p : Fin q) : position (⟨q+p.val,by have := p.isLt; dsimp [width]; omega⟩ : Fin (width q))=.palette p := by
  have := p.isLt
  simp [position,show ¬q+p.val<q by omega,show q+p.val<2*q by omega]

lemma encoded_colors (u : Fin n → Fin d → ZMod 2) (b : Fin n) :
    colors (encoded (q:=q) u) b=List.finRange q := by
  rw [←List.ofFn_id]
  apply congrArg List.ofFn
  funext p
  rw [palCell,encoded_cell,pal_position]
  rfl

lemma clean_colors {S : Schedule q} (u : Fin n → Fin d → ZMod 2) (g : Fin (n*width q) → Cell q)
    (hr : Reach S d (encodeWord (List.ofFn u)) (List.ofFn g)) (b : Fin n) :
    (colors g b).Nodup ∧ ∀x,x∈colors g b := by
  rw [←encoded_ofFn] at hr
  have hh := colors_reach (layout_encoded u) hr b
  rw [encoded_colors] at hh
  exact ⟨hh.nodup_iff.mp (List.nodup_finRange q),fun x => hh.mem_iff.mp (List.mem_finRange x)⟩

lemma checker_adjacent {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hs : Syntax S d (List.ofFn f)) (i j : Fin (n*width q)) (hij : i.val+1=j.val) :
    CheckerPair (f i) (f j) := by
  have hh := List.isChain_ofFn.mp hs.2.1 i.val (by rw [hij]; exact j.isLt)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact Fin.ext hij.symm

lemma paletteView_syntax {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hl : Layout f) (hs : Syntax S d (List.ofFn f)) (b : Fin n) :
    Palette.Syntax (paletteView f b) := by
  constructor
  · apply List.isChain_ofFn.mpr
    intro p hp
    have hh := checker_adjacent hs (palCell b ⟨p,by omega⟩) (palCell b ⟨p+1,hp⟩) (by simp [palCell,cell,Nat.add_assoc])
    exact hh.1 ⟨palCell_palette hl _ _,palCell_palette hl _ _⟩
  · intro c hc
    have he : paletteView f b≠[] := by simp [paletteView,NeZero.ne q]
    rw [List.getLast?_eq_some_getLast he] at hc
    simp only [paletteView,List.getLast_ofFn,Option.mem_def,Option.some.injEq] at hc
    subst c
    let p : Fin q := ⟨q-1,by have := NeZero.pos q; omega⟩
    let z : Fin (n*width q) := cell b ⟨2*q,by simp [width]⟩
    have hpos : (f z).pos=.stop := by rw [layout_stop_iff hl]; exact congrArg Fin.val (coord_cell _ _)
    have hh := checker_adjacent hs (palCell b p) z (by
      have := NeZero.pos q
      dsimp [palCell,cell,z,p]
      omega)
    exact hh.2 ⟨palCell_palette hl _ _,hpos⟩

lemma palette_equal_colors_absurd {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (hn : ∀b,(colors f b).Nodup) (i j : Fin (n*width q)) (hij : i.val+1=j.val)
    (x : Fin q) (hi : (f i).pos=.palette x) (hj : (f j).pos=.palette x) : False := by
  have hb := adjacent_palettes_block hl i j hij ⟨x,hi⟩
  let pi := palOffset hl i ⟨x,hi⟩
  let pj := palOffset hl j ⟨x,hj⟩
  have hei : palCell (block i) pi=i := palOffset_cell hl i ⟨x,hi⟩
  have hej : palCell (block i) pj=j := by rw [hb]; exact palOffset_cell hl j ⟨x,hj⟩
  have hc : (f (palCell (block i) pi)).color=(f (palCell (block i) pj)).color := by
    rw [hei,hej,Cell.color_eq _ _ hi,Cell.color_eq _ _ hj]
  have he := List.nodup_ofFn.mp (hn (block i)) hc
  have hh : i=j := hei.symm.trans ((congrArg (palCell (block i)) he).trans hej)
  have hv := congrArg Fin.val hh
  omega

end Rigid
end

open LocalSyntax LocalSyntax.Skeleton
namespace Rigid
variable {q d n : ℕ} [NeZero q]

lemma paletteView_safe {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (hsafe : ∀i,(f i).CheckerSafe) (b : Fin n) : Palette.Safe (paletteView f b) := by
  rintro c hc x hcheck hcolor
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hc
  obtain ⟨v,hpos⟩ := palCell_palette hl b p
  have hsv := hsafe (palCell b p)
  have hpx : (f (palCell b p)).pos=.palette x := by
    rw [hpos]
    apply congrArg Position.palette
    exact (Cell.color_eq _ _ hpos).symm.trans hcolor
  exact hsv x hpx hcheck

lemma paletteView_nonzero {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hl : Layout f) (hs : Syntax S d (List.ofFn f)) (hsafe : ∀i,(f i).CheckerSafe)
    (hcolors : ∀b,(colors f b).Nodup ∧ ∀x,x∈colors f b) (b : Fin n) :
    ¬Palette.Zero (paletteView f b) := by
  apply Palette.not_zero_of_invariants (paletteView_syntax hl hs b) (paletteView_safe hl hsafe b)
  · simpa [paletteView,List.map_ofFn,viewCell,colors,Function.comp_def] using (hcolors b).1
  · simpa [paletteView,List.map_ofFn,viewCell,colors,Function.comp_def] using (hcolors b).2

lemma palette_stop_last {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (i j : Fin (n*width q)) (hij : i.val+1=j.val) (hi : (f i).isPalette)
    (hj : (f j).pos=.stop) :
    i=palCell (block i) ⟨q-1,by have := NeZero.pos q; omega⟩ := by
  have hr := (layout_palette_iff hl i).mp hi
  have hjr := (layout_stop_iff hl j).mp hj
  have h1 : 1<width q := by have := NeZero.pos q; dsimp [width]; omega
  have hb : i.val%width q+1<width q := by change i.val%width q+1<2*q+1; omega
  rw [←hij,Nat.add_mod,Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt hb] at hjr
  have he := palOffset_cell hl i hi
  calc
    i = palCell (block i) (palOffset hl i hi) := he.symm
    _ = palCell (block i) ⟨q-1,by have := NeZero.pos q; omega⟩ := by
      apply congrArg (palCell (block i))
      apply Fin.ext
      change i.val%width q-q=q-1
      omega

lemma no_failed_checker {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hl : Layout f) (hs : Syntax S d (List.ofFn f)) (hsafe : ∀i,(f i).CheckerSafe)
    (hcolors : ∀b,(colors f b).Nodup ∧ ∀x,x∈colors f b)
    (i j : Fin (n*width q)) (hij : i.val+1=j.val)
    (x y : Fin q) (hix : (f i).pos=.palette x) (hiy : (f i).checker=.head y)
    (hj : (f j).pos=.stop) (hxy : x≠y) : False := by
  let b := block i
  let p : Fin q := ⟨q-1,by have := NeZero.pos q; omega⟩
  have hei : palCell b p=i := (palette_stop_last hl i j hij ⟨x,hix⟩ hj).symm
  apply paletteView_nonzero hl hs hsafe hcolors b
  right; right
  refine ⟨(paletteView f b).take (q-1),viewCell f b p,y,?_,?_,?_⟩
  · have hh := ofFn_split_one (viewCell f b) p
    have hp : p.val+1=q := by have := NeZero.pos q; dsimp [p]; omega
    rw [hp,List.drop_eq_nil_of_le (by simp)] at hh
    simpa [paletteView,p] using hh
  · change (f (palCell b p)).checker=.head y
    rwa [hei]
  · change (f (palCell b p)).color≠y
    rwa [hei,Cell.color_eq _ _ hix]

lemma no_binaryZero {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hl : Layout f) (hs : Syntax S d (List.ofFn f)) (hsafe : ∀i,(f i).CheckerSafe)
    (hcolors : ∀b,(colors f b).Nodup ∧ ∀x,x∈colors f b)
    (i j : Fin (n*width q)) (hij : i.val+1=j.val) : ¬BinaryZero (f i) (f j) := by
  rintro (hp|⟨x,hi,hj⟩|⟨x,y,hi,hhead,hstop,hxy⟩)
  · exact hp ⟨Verification.coherent_of_syntax S hs i j hij,checker_adjacent hs i j hij⟩
  · exact palette_equal_colors_absurd hl (fun b => (hcolors b).1) i j hij x hi hj
  · exact no_failed_checker hl hs hsafe hcolors i j hij x y hi hhead hstop hxy

lemma unaryZero_semantic {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hs : Syntax S d (List.ofFn f)) (hsafe : ∀i,(f i).CheckerSafe)
    (i : Fin (n*width q)) (hz : UnaryZero S d (f i)) : SemanticZero S (f i) := by
  rcases hz with hf|hz|⟨x,hp,hc⟩
  · exact (hf (hs.2.2 (f i) (List.mem_ofFn.mpr ⟨i,rfl⟩))).elim
  · exact hz
  · exact (hsafe i x hp hc).elim

theorem contextualZero_checked {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hd : d≤q) (hl : Layout f) (hs : Syntax S d (List.ofFn f))
    (hg : Verification.AllGood S f) (hsafe : ∀i,(f i).CheckerSafe)
    (hcolors : ∀b,(colors f b).Nodup ∧ ∀x,x∈colors f b)
    (p z t : List (Cell q)) (hw : List.ofFn f=p++z++t) (hz : Zero S d z) :
    CheckedZero S hd (List.ofFn (decoded hd f)) := by
  rcases hz with ⟨a,rfl,ha⟩|⟨a,b,rfl,hab⟩
  · have hn := congrArg List.length hw
    simp only [List.length_ofFn,List.length_append,List.length_singleton] at hn
    let i : Fin (n*width q) := ⟨p.length,by omega⟩
    have hi : f i=a := by simpa using Verification.get_of_context hw i 0 (by simp) (by simp [i])
    exact semanticZero_checked hd hl hs hg i (unaryZero_semantic hs hsafe i (hi ▸ ha))
  · have hn := congrArg List.length hw
    simp only [List.length_ofFn,List.length_append,List.length_cons,List.length_nil] at hn
    let i : Fin (n*width q) := ⟨p.length,by omega⟩
    let j : Fin (n*width q) := ⟨p.length+1,by omega⟩
    have hi : f i=a := by simpa using Verification.get_of_context hw i 0 (by simp) (by simp [i])
    have hj : f j=b := by simpa using Verification.get_of_context hw j 1 (by simp) (by simp [j])
    exact ((no_binaryZero hl hs hsafe hcolors i j rfl) (by rwa [hi,hj])).elim

theorem clean_zero_decodes {S : Schedule q} (hd : d≤q)
    (u : Fin n → Fin d → ZMod 2) (p z t : List (Cell q))
    (hr : Reach S d (encodeWord (List.ofFn u)) (p++z++t)) (hz : Zero S d z) :
    ∃ v, CheckedReach S hd (List.ofFn u) v ∧ CheckedZero S hd v := by
  let w := p++z++t
  have hn : w.length=n*width q := by
    have hh := reach_length hr
    simpa [w,encodeWord_length,width,Nat.mul_comm] using hh.symm
  let g : Fin (n*width q) → Cell q := fun i => w.get (Fin.cast hn.symm i)
  have hg : List.ofFn g=w := by
    rw [show g=(fun i => w.get (Fin.cast hn.symm i)) from rfl,
      ←List.ofFn_congr hn w.get]
    exact List.ofFn_get w
  have hr' : Reach S d (encodeWord (List.ofFn u)) (List.ofFn g) := by rwa [hg]
  have hs : Syntax S d (List.ofFn g) := reach_syntax hr' (encodeWord_syntax _)
  have he : Reach S d (List.ofFn (encoded (q:=q) u)) (List.ofFn g) := by
    rwa [encoded_ofFn]
  have hl := layout_reach (layout_encoded u) he
  have hv : Verification.AllGood S g :=
    (Verification.wordGood_ofFn S g).mp ((Verification.wordGood_reach S
      (by rw [encoded_ofFn]; exact encodeWord_syntax _) he).mp
      ((Verification.wordGood_ofFn S (encoded (q:=q) u)).mpr
        (Verification.allGood_of_idle S (encoded u) (encoded_idle u))))
  have hsafe : ∀i,(g i).CheckerSafe := by
    intro i
    exact (checkerSafe_reach hr').mp (encodeWord_checkerSafe _) _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  exact ⟨List.ofFn (decoded hd g),clean_decoded_reach hd u g hr',
    contextualZero_checked hd hl hs hv hsafe (clean_colors u g hr') p z t hg hz⟩

theorem clean_survives {S : Schedule q} (hd : d≤q) (u : List (Fin d → ZMod 2))
    (hu : ∀v, CheckedReach S hd u v → ¬CheckedZero S hd v) :
    Survives S d (encodeWord u) := by
  intro p z t hr hz
  have hr' : Reach S d (encodeWord (List.ofFn u.get)) (p++z++t) := by simpa using hr
  obtain ⟨v,hv,hzv⟩ := clean_zero_decodes hd u.get p z t hr' hz
  exact hu v (by simpa using hv) hzv

end Rigid
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TemplateHierarchy
attribute [-instance] _root_.OAI.SourceBurnside.SourceMachine.MachineHierarchy.token_finite _root_.OAI.SourceBurnside.SourceMachine.MachineHierarchy.token_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable FiniteTable.Codec
variable {q d h D : ℕ} [NeZero q]
lemma physical_assemble (R : Region q d) :
    physicalBits R=Layout.assemble (regionData R) (regionCert R) := by
  funext a
  cases a <;> rfl
lemma candidate_region (R : Region q (10000*h)) (hdq : 10000*h≤q)
    (hl10 : R.task.arity.val+1≤10) (s : Bool) :
    List.ofFn (candidateWord (l:=R.task.arity.val+1) (regionData R) hdq hl10 s)=
      (R.dataWord hdq s).map (fun w j => Addressable.unbit (w j)) := by
  rw [Region.dataWord,List.map_ofFn]
  congr 1
  funext b p
  simp only [candidateWord,regionData,physicalBits,Region.read]
  simp only [show b.val<R.task.arity.val+1 from b.isLt,dite_eq_left]
  rfl

end
end SourceBurnside.SourceMachine

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax
variable {h d : ℕ}
lemma split_encoding {α γ : Type*} {f : α→γ} {v : List α} {p a s : List γ}
    (hv : v.map f=p++a++s) : ∃p' a' s', v=p'++a'++s' ∧ p'.map f=p ∧ a'.map f=a ∧ s'.map f=s := by
  obtain ⟨u,s',rfl,hu,hs⟩ := List.map_eq_append_iff.mp hv
  obtain ⟨p',a',rfl,hp,ha⟩ := List.map_eq_append_iff.mp hu
  exact ⟨p',a',s',rfl,hp,ha,hs⟩
lemma step_from_encoding (hh : 4≤h) {S : Schedule (2^h)} {v : List (Cell (2^h))}
    {w : List (Raw h)} (he : Step (by omega) S d (v.map encode) w) :
    ∃ w', w=w'.map encode ∧ FiniteTable.Step S d v w' := by
  obtain ⟨p,s,a,b,hv,rfl,he⟩ := he
  obtain ⟨p',a',s',rfl,hp,ha,hs⟩ := split_encoding hv
  obtain ⟨_,b',_,hb,_⟩ := replacement_has_encodings hh S d a b he
  refine ⟨p'++b'++s',by simp [hp,hb,hs],p',s',a',b',rfl,rfl,?_⟩
  apply (replacement_encode hh S d a' b').mp
  simpa only [ha,←hb] using he
lemma reach_from_encoding (hh : 4≤h) {S : Schedule (2^h)} {v : List (Cell (2^h))}
    {w : List (Raw h)} (he : Reach (by omega) S d (v.map encode) w) :
    ∃ w', w=w'.map encode ∧ FiniteTable.Reach S d v w' := by
  induction he with
  | refl => exact ⟨v,rfl,.refl⟩
  | tail h e ih =>
    obtain ⟨u,rfl,hu⟩ := ih
    obtain ⟨w',rfl,he⟩ := step_from_encoding hh e
    exact ⟨w',rfl,hu.tail he⟩
lemma survives_encode_iff (hh : 4≤h) {S : Schedule (2^h)} (w : List (Cell (2^h))) :
    Survives (by omega) S d (w.map encode) ↔ FiniteTable.Survives S d w := by
  constructor
  · intro hw p z s hr hz
    exact hw (p.map encode) (z.map encode) (s.map encode)
      (by simpa using reach_encode hh hr) ((zero_encode hh S d z).mpr hz)
  · intro hw p z s hr hz
    obtain ⟨v,hv,hr⟩ := reach_from_encoding hh hr
    obtain ⟨p',z',s',rfl,hp,hz',hs⟩ := split_encoding hv.symm
    apply hw p' z' s' hr
    apply (zero_encode hh S d z').mp
    simpa only [hz'] using hz
end SourceBurnside.FiniteTable.Codec

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable
variable {q H h D : ℕ} [NeZero q]
lemma checkedSwap_raw {S : Schedule q} {T : Schedule (2^H)} (hh : 0<H)
    (hd : 10000*H≤q) (d' : ℕ)
    (law : ∀ R : Region q (10000*H), (∀j,(R.plan S).Holds j) →
      Codec.entry hh T d' R.task.zeroTask ((R.dataWord hd false).map bits)
        (if R.task.zeroTask then [] else (R.dataWord hd true).map bits)=true)
    {v w : List (Fin (10000*H)→ZMod 2)} (he : CheckedSwap S hd v w) :
    Codec.Step hh T d' (v.map bits) (w.map bits) := by
  cases he with
  | mk R s hz hc p t =>
    have he := law R hc
    simp only [hz,Bool.false_eq_true,ite_false] at he
    have he := (Codec.entry_replacement hh T d' _ _).mp he
    cases s
    · exact ⟨p.map bits,t.map bits,(R.dataWord hd false).map bits,
        (R.dataWord hd true).map bits,by simp,by simp,he⟩
    · exact ⟨p.map bits,t.map bits,(R.dataWord hd true).map bits,
        (R.dataWord hd false).map bits,by simp,by simp,(Codec.replacement_symm hh T d' _ _).mp he⟩
lemma checkedReach_raw {S : Schedule q} {T : Schedule (2^H)} (hh : 0<H)
    (hd : 10000*H≤q) (d' : ℕ)
    (law : ∀ R : Region q (10000*H), (∀j,(R.plan S).Holds j) →
      Codec.entry hh T d' R.task.zeroTask ((R.dataWord hd false).map bits)
        (if R.task.zeroTask then [] else (R.dataWord hd true).map bits)=true)
    {v w : List (Fin (10000*H)→ZMod 2)} (he : CheckedReach S hd v w) :
    Codec.Reach hh T d' (v.map bits) (w.map bits) := by
  induction he with
  | refl => exact .refl
  | tail h e ih => exact ih.tail (checkedSwap_raw hh hd d' law e)
lemma checkedZero_raw {S : Schedule q} {T : Schedule (2^H)} (hh : 0<H)
    (hd : 10000*H≤q) (d' : ℕ)
    (law : ∀ R : Region q (10000*H), (∀j,(R.plan S).Holds j) →
      Codec.entry hh T d' R.task.zeroTask ((R.dataWord hd false).map bits)
        (if R.task.zeroTask then [] else (R.dataWord hd true).map bits)=true)
    {w : List (Fin (10000*H)→ZMod 2)} (he : CheckedZero S hd w) :
    ∃p z t, w.map bits=p++z++t ∧ Codec.zero hh T d' z := by
  obtain ⟨R,p,t,hz,hc,rfl⟩ := he
  have he := law R hc
  simp only [hz,ite_true] at he
  exact ⟨p.map bits,(R.dataWord hd false).map bits,t.map bits,by simp,
    ((Codec.entry_zero hh T d' _ _).mp he).2⟩
lemma clean_nonzero {S : Schedule q} {T : Schedule (2^H)} (hh : 0<H)
    (hd : 10000*H≤q) (d' : ℕ)
    (law : ∀ R : Region q (10000*H), (∀j,(R.plan S).Holds j) →
      Codec.entry hh T d' R.task.zeroTask ((R.dataWord hd false).map bits)
        (if R.task.zeroTask then [] else (R.dataWord hd true).map bits)=true)
    (w : List (Codec.Raw H)) (hw : Codec.Survives hh T d' w) :
    FiniteTable.Survives S (10000*H) (encodeWord (w.map scalars)) := by
  apply Rigid.clean_survives hd
  intro v hv hz
  have hr := checkedReach_raw hh hd d' law hv
  have hh' : (w.map scalars).map bits=w := by simp [List.map_map,Function.comp_def]
  rw [hh'] at hr
  obtain ⟨p,z,t,hv,hz⟩ := checkedZero_raw hh hd d' law hz
  exact hw p z t (by rwa [hv] at hr) hz

end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable

namespace MachineHierarchy
variable {D : ℕ} {hD : 2≤D} (A : MachineHierarchy D hD)
lemma region_entry {h : ℕ} (hh : A.threshold≤h) (R : Region (2^h) (10000*(D*h)))
    (hc : ∀j,(R.plan (A.schedule h hh)).Holds j) :
    Codec.entry (A.height_pos (A.next_large hh)) (A.schedule (D*h) (A.next_large hh)) (10000*(D*(D*h)))
      R.task.zeroTask ((R.dataWord (A.fits h hh).2.2.2.1 false).map bits)
      (if R.task.zeroTask then [] else (R.dataWord (A.fits h hh).2.2.2.1 true).map bits)=true := by
  have hc' := (physical_clauses_iff _ _ _ _ _ _ R).mp hc
  rw [physical_assemble R] at hc'
  have he := (A.certifies h hh R.task (regionData R)).mp ⟨regionCert R,hc'⟩
  rw [candidate_region R (A.fits h hh).2.2.2.1 _ false,
    candidate_region R (A.fits h hh).2.2.2.1 _ true] at he
  exact he

theorem faithful {h : ℕ} (hh : A.threshold≤h) (w : List (Codec.Raw (D*h)))
    (hw : Codec.Survives (A.height_pos (A.next_large hh)) (A.schedule (D*h) (A.next_large hh))
      (10000*(D*(D*h))) w) :
    Codec.Survives (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) (embedding h D w) := by
  apply (Codec.survives_encode_iff (by have := A.threshold_four;omega) _).mpr
  exact clean_nonzero (A.height_pos (A.next_large hh)) (A.fits h hh).2.2.2.1 _
    (A.region_entry hh) w hw

end MachineHierarchy
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable
lemma idleCore_survives {q : ℕ} [NeZero q] (S : Schedule q) (d : ℕ) (p : Fin q) (hp : p.val≠0) :
    FiniteTable.Survives S d [idleCore p] := by
  intro l z r hr hz
  have he := (reach_interior_idle_iff (by rfl : (idleCore p).marker=.idle)
    ⟨p,rfl,hp⟩ _).mp hr
  exact idleCore_not_contextual_zero S d p l z r hz he.symm
namespace MachineHierarchy
variable {D : ℕ} {hD : 2≤D} (A : MachineHierarchy D hD)
theorem nonzero_letter {h : ℕ} (hh : A.threshold≤h) :
    ∃c : Codec.Raw h, Codec.Survives (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) [c] := by
  have h4 : 4≤h := A.threshold_four.trans hh
  have hq : 1<2^h := Nat.one_lt_two_pow_iff.mpr (by omega)
  let p : Fin (2^h) := ⟨1,hq⟩
  refine ⟨Codec.encode (idleCore p),?_⟩
  exact (Codec.survives_encode_iff h4 [idleCore p]).mpr (idleCore_survives _ _ p (by change (1:ℕ)≠0;omega))

theorem unbounded_survivors (n : ℕ) : ∀(h : ℕ) (hh : A.threshold≤h),
    ∃w : List (Codec.Raw h), n<w.length ∧
      Codec.Survives (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) w := by
  induction n with
  | zero =>
    intro h hh
    obtain ⟨c,hc⟩ := A.nonzero_letter hh
    exact ⟨[c],by simp,hc⟩
  | succ n ih =>
    intro h hh
    obtain ⟨w,hw,hs⟩ := ih (D*h) (A.next_large hh)
    refine ⟨embedding h D w,?_,A.faithful hh w hs⟩
    rw [embedding_length]
    have hq : 0<2^h := by positivity
    nlinarith
end MachineHierarchy
end
end SourceBurnside.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_WordAlgebra
attribute [-instance] _root_.OAI.SourceBurnside.SourceMachine.MachineHierarchy.token_finite _root_.OAI.SourceBurnside.SourceMachine.MachineHierarchy.token_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.WordAlgebra

noncomputable section
open Classical

variable {α : Type u} {K : Type v} [Ring K]

namespace Table

variable (T : Table α)

lemma reach_context {v w : Word α} (h : T.Reach v w) (p s : Word α) :
    T.Reach (p * v * s) (p * w * s) :=
  (conGen T.rep).mul ((conGen T.rep).mul ((conGen T.rep).refl p) h)
    ((conGen T.rep).refl s)

lemma detect_eq_of_reach (target : Word α) {v w : Word α} (h : T.Reach v w) (a : K) :
    T.detect target (MonoidAlgebra.single v a) =
      T.detect target (MonoidAlgebra.single w a) := by
  classical
  have he : T.Reach target v ↔ T.Reach target w :=
    ⟨fun ht => (conGen T.rep).trans ht h,
     fun ht => (conGen T.rep).trans ht ((conGen T.rep).symm h)⟩
  simp only [detect_single, he]

lemma relation_in_annihilator (target : Word α) (hnz : ¬ T.Vanishes target)
    {f : Polynomial K α} (hf : f ∈ T.relations) : f ∈ annihilator (T.detect target) := by
  classical
  apply (mem_annihilator _ _).mpr
  intro A B
  induction A using MonoidAlgebra.induction_linear with
  | zero => simp
  | add A₁ A₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | single p a =>
    induction B using MonoidAlgebra.induction_linear with
    | zero => simp
    | add B₁ B₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | single s b =>
      rcases hf with ⟨v, w, hvw, rfl⟩ | ⟨z, hz, rfl⟩
      · simp only [monomial, mul_sub, sub_mul, MonoidAlgebra.single_mul_single,
          mul_one, map_sub]
        exact sub_eq_zero.mpr (T.detect_eq_of_reach target
          (T.reach_context (ConGen.Rel.of _ _ hvw) p s) (a * b))
      · simp only [monomial, MonoidAlgebra.single_mul_single, mul_one, detect_single]
        apply ite_eq_right
        intro hr
        exact hnz ⟨p, z, s, hz, hr⟩

lemma ideal_le_annihilator (target : Word α) (hnz : ¬ T.Vanishes target) :
    T.ideal (K := K) ≤ annihilator (T.detect target) :=
  TwoSidedIdeal.span_le.mpr (fun _ hf => T.relation_in_annihilator target hnz hf)

theorem word_ne_zero [Nontrivial K] {w : Word α} (hw : ¬ T.Vanishes w) :
    T.word (K := K) w ≠ 0 := by
  intro h
  have hm : monomial (K := K) w ∈ T.ideal := ((T.ideal (K := K)).ringCon.eq).mp h
  have hd := (mem_annihilator (T.detect w) _).mp (T.ideal_le_annihilator w hw hm) 1 1
  simp only [one_mul, mul_one, detect_self] at hd
  exact one_ne_zero hd

theorem word_eq_zero_iff [Nontrivial K] (w : Word α) :
    T.word (K := K) w = 0 ↔ T.Vanishes w :=
  ⟨fun h => by by_contra hn; exact T.word_ne_zero hn h, T.word_eq_zero_of_vanishes⟩

theorem word_eq_word_iff [Nontrivial K] (v w : Word α) :
    T.word (K := K) v = T.word w ↔
      T.Reach v w ∨ (T.Vanishes v ∧ T.Vanishes w) := by
  constructor
  · intro h
    by_cases hv : T.Vanishes v
    · right
      exact ⟨hv, (T.word_eq_zero_iff w).mp (h.symm.trans (T.word_eq_zero_of_vanishes hv))⟩
    · left
      by_contra hr
      have hm : monomial (K := K) v - monomial w ∈ T.ideal :=
        ((T.ideal (K := K)).rel_iff _ _).mp (((T.ideal (K := K)).ringCon.eq).mp h)
      have hd := (mem_annihilator (T.detect v) _).mp
        (T.ideal_le_annihilator v hv hm) 1 1
      simp only [one_mul, mul_one, map_sub, monomial, detect_single,
        ite_eq_left ((conGen T.rep).refl v), ite_eq_right hr, sub_zero] at hd
      exact one_ne_zero hd
  · rintro (hr | ⟨hv, hw⟩)
    · exact T.word_reach hr
    · exact (T.word_eq_zero_of_vanishes hv).trans (T.word_eq_zero_of_vanishes hw).symm

lemma length_eq_of_reach (hh : T.Homogeneous) {v w : Word α} (h : T.Reach v w) :
    v.length = w.length := by
  let C : Con (Word α) :=
    { r := fun v w => v.length = w.length
      iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
      mul' := by intro a b c d h₁ h₂; simp only [FreeMonoid.length_mul, h₁, h₂] }
  have hC : conGen T.rep ≤ C := Con.conGen_le.mpr hh
  exact hC h

theorem infinite_algebra [Nontrivial K] (hh : T.Homogeneous)
    (hw : ∀ N : ℕ, ∃ w : Word α, N < w.length ∧ ¬ T.Vanishes w) :
    Infinite (T.Algebra (K := K)) := by
  obtain ⟨φ, hφ, hwφ⟩ := Nat.exists_strictMono_subsequence
    (P := fun n => ∃ w : Word α, w.length = n ∧ ¬ T.Vanishes w)
    (fun N => by obtain ⟨w, hn, hsurv⟩ := hw N; exact ⟨w.length, hn, w, rfl, hsurv⟩)
  choose w hwlen hwsurv using hwφ
  apply Infinite.of_injective (fun n => T.word (K := K) (w n))
  intro m n he
  rcases (T.word_eq_word_iff _ _).mp he with hreach | hzero
  · apply hφ.injective
    simpa only [hwlen] using T.length_eq_of_reach hh hreach
  · exact (hwsurv m hzero.1).elim

end Table

end

end SourceBurnside.WordAlgebra

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
lemma survives_iff_not_vanishes (w : List (Raw h)) :
    Survives hh S d w ↔ ¬(algebraTable hh S d).Vanishes (FreeMonoid.ofList w) := by
  constructor
  · intro hw ⟨p,z,s,hz,hr⟩
    have he : Reach hh S d w (p.toList++z.toList++s.toList) := reach_iff_table.mpr hr
    exact hw p.toList z.toList s.toList he hz
  · intro hw p z s hr hz
    exact hw ⟨FreeMonoid.ofList p,FreeMonoid.ofList z,FreeMonoid.ofList s,hz,reach_iff_table.mp hr⟩
end SourceBurnside.FiniteTable.Codec
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open FiniteTable
variable {D : ℕ} {hD : 2≤D} (A : MachineHierarchy D hD)

theorem infinite_algebra (K : Type*) [Ring K] [Nontrivial K] (h : ℕ) (hh : A.threshold≤h) :
    Infinite (A.Algebra K h hh) := by
  apply (A.table h hh).infinite_algebra
  · exact Codec.algebraTable_homogeneous (A.threshold_four.trans hh)
  · intro N
    obtain ⟨w,hw,hs⟩ := A.unbounded_survivors N h hh
    exact ⟨FreeMonoid.ofList w,hw,Codec.survives_iff_not_vanishes w |>.mp hs⟩
end
end SourceBurnside.SourceMachine.MachineHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_PresentationModel
attribute [-instance] _root_.OAI.SourceBurnside.FiniteSteinbergPresentation.root_finite _root_.OAI.SourceBurnside.MonomialCompletion.rootSubgroup_comm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside

namespace Elementary

variable {n : ℕ} {R : Type u} [Ring R]

theorem e_injective (p : Root n) : Function.Injective (e p : R → _) := by
  intro a b h
  have h' := congrArg (fun g : (Matrix (Fin n) (Fin n) R)ˣ => g.val p.row p.col) h
  simpa [coe_e, p.ne] using h'

theorem x_injective (p : Root n) : Function.Injective (Steinberg.x p : R → _) := by
  intro a b h
  apply e_injective p
  simpa using congrArg representation h

theorem steinberg_infinite [Infinite R] (p : Root n) : Infinite (Steinberg n R) :=
  Infinite.of_injective _ (x_injective p)

end Elementary

end SourceBurnside

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_CoefficientQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)

theorem steinberg_infinite {h : ℕ} (hh : A.threshold ≤ h) :
    Infinite (Steinberg 12 (A.Algebra (ZMod 2) h hh)) := by
  let := A.infinite_algebra (ZMod 2) h hh
  exact Elementary.steinberg_infinite ⟨0,1,by decide⟩

end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside.ConcreteSource
noncomputable section

instance ring_infinite : Infinite R := machine.infinite_algebra (ZMod 2) height (by rfl)
instance characteristic : CharP R 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) R).injective 2

theorem steinberg_infinite_oai : Infinite (Steinberg 12 R) := machine.steinberg_infinite (by rfl)

end
end SourceBurnside.ConcreteSource

end

end OAI
end

theorem solution : type_of% @OAI.SourceBurnside.ConcreteSource.steinberg_infinite_oai := @OAI.SourceBurnside.ConcreteSource.steinberg_infinite_oai
