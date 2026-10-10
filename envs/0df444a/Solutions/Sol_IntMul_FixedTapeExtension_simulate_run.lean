-- Prove2me | solution 1 for IntMul.FixedTapeExtension.simulate_run
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T23:59:36.021044+00:00
-- url     : https://prove2.me/submissions/f03bd9f6-4ffe-4a3c-a3ff-c1110fe474a9

import Definitions.Def_IntMul_FixedTapeExtension
import Mathlib.Tactic


namespace IntMul.FixedTapeExtension

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem inner_old (M : MultitapeTM) (j : Fin M.k) (h : (oldTape M j).val < M.k) :
    innerTape M (oldTape M j) h = j := by apply Fin.ext; rfl

private theorem old_bound (M : MultitapeTM) (j : Fin M.k) : (oldTape M j).val < M.k := j.isLt

/-- Each old machine transition is copied literally while the added tape
retains every cell and its head. No extra tape movement is hidden. -/
private theorem step_embed (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) :
    (machine M).step (embed M base c) = embed M base (M.step c) := by
  have hscan : (fun j => (embed M base c).cells (oldTape M j) ((embed M base c).head (oldTape M j))) =
      (fun j => c.cells j (c.head j)) := by
    funext j
    simp only [embed,dif_pos (old_bound M j),inner_old]
  have ht : transition M (embed M base c).state
      (fun i => (embed M base c).cells i ((embed M base c).head i)) =
      ((M.δ c.state (fun j => c.cells j (c.head j))).1,
        fun i => if h : i.val < M.k then
          (M.δ c.state (fun j => c.cells j (c.head j))).2 (innerTape M i h)
        else ((embed M base c).cells i ((embed M base c).head i),.stay)) := by
    dsimp only [transition]
    rw [hscan]
    rfl
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val < M.k
    · simp only [dif_pos hi,embed,dif_pos hi,MultitapeTM.step]
    · simp only [dif_neg hi,embed,dif_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val < M.k
    · simp only [dif_pos hi,embed,dif_pos hi,MultitapeTM.step]
    · simp only [dif_neg hi,embed,dif_neg hi]

private theorem iterate_embed (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) (T : ℕ) :
    (machine M).step^[T] (embed M base c) = embed M base (M.step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,step_embed,Function.iterate_succ_apply']

/-- Arbitrary saved extra-tape contents and head are preserved for the full
run, with the original finite control, alphabet and exact clock unchanged. -/
private theorem simulate_run (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) (T : ℕ) :
    (machine M).step^[T] (embed M base c) = embed M base (M.step^[T] c) ∧
    ((machine M).step^[T] (embed M base c)).cells (extraTape M) = base.cells (extraTape M) ∧
    ((machine M).step^[T] (embed M base c)).head (extraTape M) = base.head (extraTape M) ∧
    (∀ j, ((machine M).step^[T] (embed M base c)).cells (oldTape M j) = (M.step^[T] c).cells j) ∧
    (∀ j, ((machine M).step^[T] (embed M base c)).head (oldTape M j) = (M.step^[T] c).head j) := by
  have hr := iterate_embed M base c T
  refine ⟨hr,?_,?_,?_,?_⟩
  · rw [hr]
    simp [embed,extraTape]
  · rw [hr]
    simp [embed,extraTape]
  · intro j
    rw [hr]
    simp only [embed,dif_pos (old_bound M j),inner_old]
  · intro j
    rw [hr]
    simp only [embed,dif_pos (old_bound M j),inner_old]

end IntMul.FixedTapeExtension


open IntMul IntMul.FixedTapeExtension

theorem solution (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) (T : ℕ) :
    (machine M).step^[T] (embed M base c) = embed M base (M.step^[T] c) ∧
    ((machine M).step^[T] (embed M base c)).cells (extraTape M) = base.cells (extraTape M) ∧
    ((machine M).step^[T] (embed M base c)).head (extraTape M) = base.head (extraTape M) ∧
    (∀ j, ((machine M).step^[T] (embed M base c)).cells (oldTape M j) = (M.step^[T] c).cells j) ∧
    (∀ j, ((machine M).step^[T] (embed M base c)).head (oldTape M j) = (M.step^[T] c).head j) :=
  IntMul.FixedTapeExtension.simulate_run M base c T

#print axioms solution
