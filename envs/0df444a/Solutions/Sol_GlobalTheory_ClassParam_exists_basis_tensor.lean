-- Prove2me | solution 1 for GlobalTheory.ClassParam.exists_basis_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:48.064596+00:00
-- url     : https://prove2.me/submissions/3a7ef2d2-4212-41fb-978e-171cb2a27dc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_algebraMap_tmul
import Theorems.Thm_GlobalTheory_ClassParam_map_smul_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution {ι : Type} [Fintype ι] (b : Module.Basis ι E (AdjoinRoot P)) :
    ∃ b' : Module.Basis ι (E ⊗[F] k) (AdjoinRoot P ⊗[F] k), ∀ i, b' i = b i ⊗ₜ 1 := by
  classical
  refine ⟨Module.Basis.mk (v := fun i => b i ⊗ₜ 1) ?_ ?_, fun i => Module.Basis.mk_apply _ _ _⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (TensorProduct.map ((b.coord j).restrictScalars F) LinearMap.id) hg
    simp only [map_sum, map_smul_tensor, map_zero] at this
    rw [Finset.sum_eq_single j] at this
    · simpa [← Algebra.TensorProduct.one_def] using this
    · intro i _ hij; simp [Finsupp.single_apply, hij]
    · simp
  · rintro y -
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => exact add_mem h h'
    | tmul l s =>
      rw [← b.sum_repr l, TensorProduct.sum_tmul]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : (b.repr l i • b i) ⊗ₜ[F] s = (b.repr l i ⊗ₜ[F] s) • (b i ⊗ₜ[F] (1 : k)) := by
        rw [Algebra.smul_def (b.repr l i ⊗ₜ[F] s), algebraMap_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]
        rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.ClassParam
