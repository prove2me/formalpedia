-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.exists_sum_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:25.549795+00:00
-- url     : https://prove2.me/submissions/12d1b139-1266-4a67-811f-6ed9f28912b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {F G H M V W U : Type} [Field F] [Group G] [Group H] [Group M] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution {ι : Type} (b : Module.Basis ι F V) (x : V ⊗[F] W) :
    ∃ s : Finset ι, (∀ i ∉ s, coord (b.coord i) W x = 0) ∧
      ∀ t : Finset ι, s ⊆ t → x = ∑ i ∈ t, b i ⊗ₜ coord (b.coord i) W x := by
  classical
  induction x with
  | zero => exact ⟨∅, by simp, by simp⟩
  | add x y hx hy =>
    obtain ⟨s, h1, h2⟩ := hx
    obtain ⟨s', h1', h2'⟩ := hy
    refine ⟨s ∪ s', fun i hi => ?_, fun t ht => ?_⟩
    · rw [Finset.mem_union, not_or] at hi
      rw [map_add, h1 i hi.1, h1' i hi.2, add_zero]
    · simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      rw [← h2 t (Finset.union_subset_left ht), ← h2' t (Finset.union_subset_right ht)]
  | tmul v w =>
    refine ⟨(b.repr v).support, fun i hi => ?_, fun t ht => ?_⟩
    · simp [coord, Finsupp.notMem_support_iff.1 hi]
    · have : v = ∑ i ∈ t, b.repr v i • b i := by
        conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply,
          Finsupp.sum_of_support_subset _ ht _ (by simp)]
      conv_lhs => rw [this, TensorProduct.sum_tmul]
      simp [coord, TensorProduct.smul_tmul]
end GlobalTheory.SmGL.MultiIrr
