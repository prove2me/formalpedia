-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:29:06.549481+00:00
-- url     : https://prove2.me/submissions/321feb22-45d6-4371-8d73-2a166a5f83e6

import Mathlib
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K049

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem prob_congr (μ : FiniteLaw Ω) {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω ↔ F ω) : μ.prob E = μ.prob F := by
  exact le_antisymm (μ.prob_mono fun ω => (hEF ω).mp) (μ.prob_mono fun ω => (hEF ω).mpr)

end FiniteLaw

end MetricKMedian

end OAI
end

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

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem expectation_mix (μ ν : SparseIntegerLaw α) (f : α → ℝ) :
    (mix μ ν).expectation f=(1/2)*μ.expectation f+(1/2)*ν.expectation f := by
  rw [mix,expectation_bindIndexed]
  change (∑ a : Fin 2, ((1/2:ℚ):ℝ)*(if a.val=0 then μ else ν).expectation f)=_
  norm_num [Fin.sum_univ_two]

theorem real_expect_all [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.real.expect f=μ.expectation f := by
  rw [real,FiniteLaw.expect_map]
  rfl

theorem prob_mix [Fintype α] [DecidableEq α] (μ ν : SparseIntegerLaw α)
    (P : α → Prop) [DecidablePred P] :
    (mix μ ν).real.prob P=(1/2)*μ.real.prob P+(1/2)*ν.real.prob P := by
  simp only [FiniteLaw.prob,real_expect_all,expectation_mix]

theorem prob_map [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : SparseIntegerLaw α) (f : α → β) (P : β → Prop) [DecidablePred P] :
    (μ.map f).real.prob P=μ.real.prob (fun a => P (f a)) := by
  simp only [FiniteLaw.prob,real_expect_all,expectation_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePhysicalBatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparsePhysicalBatch
open Finset
variable {n : ℕ}

theorem balanced_eq (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n)) (ω : Fin n → Bool) :
    balanced Z C ω=PhysicalBatchLaw.balanced Z C ω := by
  ext e
  simp only [balanced,PhysicalBatchLaw.balanced,FiniteLaw.selected,mem_inter,mem_filter]

theorem unbalanced_eq (Z : Finset (Fin n)) (ω : Fin n → Bool) :
    unbalanced Z ω=PhysicalBatchLaw.unbalanced Z ω := rfl

theorem prob_eq (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (R : Finset (Fin n) → Prop) [DecidablePred R] :
    (law Z C p q hp hq).real.prob R=
      (1/2)*(SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => R (PhysicalBatchLaw.balanced Z C ω))+
      (1/2)*(SparseBernoulli.run (d := 4) q hq n).real.prob
        (fun ω => R (PhysicalBatchLaw.unbalanced Z ω)) := by
  rw [law,SparseIntegerLaw.prob_mix,SparseIntegerLaw.prob_map,SparseIntegerLaw.prob_map]
  apply congrArg₂ (fun x y : ℝ => (1/2)*x+(1/2)*y)
  · apply FiniteLaw.prob_congr
    intro ω
    rw [balanced_eq]
  · apply FiniteLaw.prob_congr
    intro ω
    rw [unbalanced_eq]

end MetricKMedian.SparsePhysicalBatch

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem balanced_map (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (ω : Fin n → Bool) :
    (PhysicalBatchLaw.balanced (Z.map enum.symm.toEmbedding)
      (fun a => (C (enum a)).map enum.symm.toEmbedding) ω).map enum.toEmbedding=
      PhysicalBatchLaw.balanced Z C (fun e => ω (enum.symm e)) := by
  ext e
  simp only [mem_map_equiv,PhysicalBatchLaw.balanced,mem_inter,FiniteLaw.selected,
    mem_filter,mem_univ,true_and,Equiv.symm_symm,Equiv.apply_symm_apply]
  constructor
  · rintro ⟨⟨he,hc⟩,hz⟩
    refine ⟨⟨he,?_⟩,hz⟩
    intro j hj
    exact hc (enum.symm j) (by simpa only [Equiv.apply_symm_apply] using hj)
  · rintro ⟨⟨he,hc⟩,hz⟩
    refine ⟨⟨he,?_⟩,hz⟩
    intro j hj
    simpa only [Equiv.symm_apply_apply] using hc (enum j) hj

theorem unbalanced_map (enum : Fin n ≃ E) (Z : Finset E) (ω : Fin n → Bool) :
    (PhysicalBatchLaw.unbalanced (Z.map enum.symm.toEmbedding) ω).map enum.toEmbedding=
      PhysicalBatchLaw.unbalanced Z (fun e => ω (enum.symm e)) := by
  ext e
  simp only [mem_map_equiv,PhysicalBatchLaw.unbalanced,mem_filter,mem_univ,true_and,
    Equiv.symm_symm,Equiv.apply_symm_apply]

theorem prob_eq_s35_oai (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (R : Finset E → Prop) [DecidablePred R] :
    (law enum Z C p q hp hq).real.prob R=
      (1/2)*(SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hp)).real.prob
        (fun ω => R (PhysicalBatchLaw.balanced Z C ω))+
      (1/2)*(SparseEnumeratedBernoulli.law enum q hq).real.prob
        (fun ω => R (PhysicalBatchLaw.unbalanced Z ω)) := by
  rw [law,SparseIntegerLaw.prob_map,SparsePhysicalBatch.prob_eq,
    SparseEnumeratedBernoulli.law,SparseIntegerLaw.prob_map,
    SparseEnumeratedBernoulli.law,SparseIntegerLaw.prob_map]
  simp only [balanced_map,unbalanced_map]

end MetricKMedian.SparseEnumeratedBatch
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq_s35_oai := @OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq_s35_oai
