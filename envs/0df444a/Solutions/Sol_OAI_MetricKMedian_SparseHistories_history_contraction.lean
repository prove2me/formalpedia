-- Prove2me | solution 1 for OAI.MetricKMedian.SparseHistories.history_contraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:45:58.695931+00:00
-- url     : https://prove2.me/submissions/3e8899a1-8661-44c7-bc55-481bacb6ef5c

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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBoundedSurvival
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

theorem history_contraction_oai (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (V : ℕ → History α → ℝ) (r : ℝ) (hr : 0 ≤ r) (T : ℕ)
    (hstep : ∀ t < T, ∀ i : Fin (tree κ a t).length,
      (κ t (tree κ a t).states[i.val].1).expectation
        (fun s => V (t+1) (extend (tree κ a t).states[i.val] s)) ≤
          r*V t (tree κ a t).states[i.val]) :
    (tree κ a T).expectation (V T) ≤ r^T*V 0 (a,[]) := by
  induction T with
  | zero => simp only [tree,SparseIntegerLaw.expectation_dirac,pow_zero,one_mul,le_refl]
  | succ t ih =>
    have hi := ih (fun u hu => hstep u (hu.trans (Nat.lt_succ_self t)))
    rw [expectation_step]
    have hs := SparseIntegerLaw.expectation_mono (tree κ a t)
      (fun z => (κ t z.1).expectation (fun s => V (t+1) (extend z s)))
      (fun z => r*V t z) (hstep t (Nat.lt_succ_self t))
    have he : (tree κ a t).expectation (fun z => r*V t z)=
        r*(tree κ a t).expectation (V t) := FiniteLaw.expect_mul _ _ _
    rw [he] at hs
    exact hs.trans ((mul_le_mul_of_nonneg_left hi hr).trans_eq (by rw [pow_succ]; ring))

end MetricKMedian.SparseHistories
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseHistories.history_contraction_oai := @OAI.MetricKMedian.SparseHistories.history_contraction_oai
