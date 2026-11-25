-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Move.det_trace_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:19.714554+00:00
-- url     : https://prove2.me/submissions/22a1a72a-a241-41ae-aebc-6e49568d640c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_traceForm_nondegenerate
import Theorems.Thm_GlobalTheory_UnitLemma_exists_basis_pow_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Move
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Move
theorem _root_.solution (hP : B.P.Separable)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨b, hb⟩ := exists_basis_pow_of_separable K B hP
  have hk : ∀ k : Fin (Module.finrank K.E B.A),
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * ∑ l, v l • e l) = 0 := by
    intro k
    have := congrFun hMv k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [Finset.mul_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hall : ∀ w : B.A, Algebra.trace K.E B.A ((∑ l, v l • e l) * w) = 0 := by
    intro w
    rw [← b.sum_repr w, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, map_smul, hb k, mul_comm, hk k, smul_zero]
  have hz0 : ∑ l, v l • e l = 0 :=
    (Sandwich.traceForm_nondegenerate B hP).1 _ (fun w => by rw [Algebra.traceForm_apply]; exact hall w)
  apply hv
  apply e.equivFun.symm.injective
  rw [Module.Basis.equivFun_symm_apply, hz0, map_zero]
end GlobalTheory.UnitLemma.Move
