-- Prove2me | solution 1 for OAI.MetricKMedian.SparseHistories.count_tail_up_to_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:22:05.31775+00:00
-- url     : https://prove2.me/submissions/fbb7a9b4-0de3-4e92-9cd3-0eda98a780ad

import Mathlib
import Definitions.Def_OAIQ035K040
import Definitions.Def_OAIQ035K045

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRealExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem expectation_def (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.expectation f=∑ i : Fin μ.length, (μ.law.rational.weight i:ℝ)*f μ.states[i.val] := rfl

theorem expectation_const (μ : SparseIntegerLaw α) (c : ℝ) :
    μ.expectation (fun _ => c)=c := μ.realIndex.expect_const c

theorem expectation_add (μ : SparseIntegerLaw α) (f g : α → ℝ) :
    μ.expectation (fun a => f a+g a)=μ.expectation f+μ.expectation g :=
  μ.realIndex.expect_add _ _

theorem expectation_mono (μ : SparseIntegerLaw α) (f g : α → ℝ)
    (h : ∀ i : Fin μ.length, f μ.states[i.val] ≤ g μ.states[i.val]) :
    μ.expectation f ≤ μ.expectation g := by
  simp only [expectation_def]
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (h i) (by exact_mod_cast μ.law.rational.nonneg i)

theorem expectation_bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (f : β → ℝ) :
    (μ.bindIndexed κ).expectation f=
      ∑ a, (μ.law.rational.weight a:ℝ)*(κ a).expectation f := by
  let ρ := μ.law.rational.sigma (fun a => (κ a).law.rational)
  calc
    _ = ∑ z, (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val] := by
      unfold expectation realIndex
      change (∑ i, (((ρ.integer.reindex finSigmaFinEquiv).rational.weight i):ℝ)*
        f ((Vector.ofFn (fun j => let z := finSigmaFinEquiv.symm j;
          (κ z.1).states[z.2.val]))[i.val])) = _
      simp only [Vector.getElem_ofFn]
      change (∑ i, (ρ.integer.rational.weight (finSigmaFinEquiv.symm i):ℝ)*
        f (κ (finSigmaFinEquiv.symm i).1).states[(finSigmaFinEquiv.symm i).2.val]) = _
      simp only [RationalLaw.integer_weight]
      exact (finSigmaFinEquiv (n := fun a => (κ a).length)).symm.sum_comp
        (fun z : Sigma (fun a : Fin μ.length => Fin (κ a).length) =>
          (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val])
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [ρ,RationalLaw.sigma,Rat.cast_mul,mul_assoc,← mul_sum,expectation_def]

theorem expectation_map (μ : SparseIntegerLaw α) (g : α → β) (f : β → ℝ) :
    (μ.map g).expectation f=μ.expectation (fun a => f (g a)) := by
  simp only [expectation_def,map,Vector.getElem_map]

theorem expectation_dirac (a : α) (f : α → ℝ) :
    (dirac a).expectation f=f a := by
  simp only [expectation_def,dirac,IntegerLaw.rational]
  norm_num

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

theorem expectation_step (κ : ℕ → α → SparseIntegerLaw α) (a : α) (t : ℕ)
    (V : History α → ℝ) :
    (tree κ a (t+1)).expectation V=
      (tree κ a t).expectation (fun h => (κ t h.1).expectation (fun s => V (extend h s))) := by
  rw [tree,SparseIntegerLaw.expectation_bindIndexed]
  simp_rw [branch,SparseIntegerLaw.expectation_map]
  rfl

end MetricKMedian.SparseHistories
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBoundedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

theorem count_tail_up_to_s35_oai (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (size : α → ℝ) (c ρ : ℝ)
    (T : ℕ)
    (hstep : ∀ t < T, ∀ i : ℕ, ∀ hi : i < (tree κ a t).length,
      (κ t (tree κ a t).states[i].1).expectation
        (fun s => if size (tree κ a t).states[i].1+c < size s then 1 else 0) ≤ ρ)
    :
    (tree κ a T).expectation (fun h => if size a+(T:ℝ)*c < size h.1 then 1 else 0) ≤
      (T:ℝ)*ρ := by
  classical
  induction T with
  | zero => simp only [tree,SparseIntegerLaw.expectation_dirac,Nat.cast_zero,zero_mul,add_zero,
      lt_self_iff_false,ite_false,le_refl]
  | succ t ih =>
    have hi := ih (fun r hr => hstep r (hr.trans (Nat.lt_succ_self t)))
    rw [expectation_step]
    have hs : ∀ i : Fin (tree κ a t).length,
        (κ t (tree κ a t).states[i.val].1).expectation
          (fun s => if size a+((t+1:ℕ):ℝ)*c < size s then 1 else 0) ≤
        (if size a+(t:ℝ)*c < size (tree κ a t).states[i.val].1 then 1 else 0)+ρ := by
      intro i
      let z := (tree κ a t).states[i.val].1
      have hp : ∀ s, (if size a+((t+1:ℕ):ℝ)*c < size s then (1:ℝ) else 0) ≤
          (if size a+(t:ℝ)*c < size z then 1 else 0)+
            (if size z+c < size s then 1 else 0) := by
        intro s
        split_ifs <;> push_cast at * <;> linarith
      have he := SparseIntegerLaw.expectation_mono (κ t z)
        (fun s => if size a+((t+1:ℕ):ℝ)*c < size s then 1 else 0)
        (fun s => (if size a+(t:ℝ)*c < size z then 1 else 0)+
          (if size z+c < size s then 1 else 0)) (fun b => hp _)
      rw [SparseIntegerLaw.expectation_add,SparseIntegerLaw.expectation_const] at he
      exact he.trans (add_le_add le_rfl (hstep t (Nat.lt_succ_self t) i.val i.isLt))
    have he := SparseIntegerLaw.expectation_mono (tree κ a t)
      (fun z => (κ t z.1).expectation
        (fun s => if size a+((t+1:ℕ):ℝ)*c < size s then 1 else 0))
      (fun z => (if size a+(t:ℝ)*c < size z.1 then 1 else 0)+ρ) hs
    rw [SparseIntegerLaw.expectation_add,SparseIntegerLaw.expectation_const] at he
    exact he.trans (by push_cast; nlinarith only [hi])

end MetricKMedian.SparseHistories
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseHistories.count_tail_up_to_s35_oai := @OAI.MetricKMedian.SparseHistories.count_tail_up_to_s35_oai
