-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Move.sgnLat_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:04.685807+00:00
-- url     : https://prove2.me/submissions/4c558dc4-0f64-4be2-9a19-fa3f6226ca86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Move_det_trace_ne_zero
import Theorems.Thm_GlobalTheory_GaloisDescentLattice_exists_fixed_basis
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_mul
import Theorems.Thm_GlobalTheory_UnitLemma_SgnBasis_sgnLat_span_basis


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
theorem _root_.solution (hP : B.P.Separable) (M : Submodule K.O B.A) (hM : IsLat K.O K.E M)
    (hσ : ∀ y ∈ M, B.σ y ∈ M) (y : B.Aˣ) :
    B.sgnLat (mulLat K.O (y : B.A) M) = K.eta (Algebra.norm K.E (y : B.A)) * B.sgnLat M := by
  classical
  obtain ⟨e, he, -⟩ := GlobalTheory.GaloisDescentLattice.exists_fixed_basis K B M hM hσ
  let f : B.A ≃ₗ[K.E] B.A := LinearEquiv.ofLinear (LinearMap.mulLeft K.E (y : B.A))
    (LinearMap.mulLeft K.E ((y⁻¹ : B.Aˣ) : B.A)) (by ext x; simp) (by ext x; simp)
  let e' := e.map f
  have he' : ∀ l, e' l = (y : B.A) * e l := fun l => rfl
  have hspan : mulLat K.O (y : B.A) M = Submodule.span K.O (Set.range e') := by
    rw [← he, mulLat, Submodule.map_span, ← Set.range_comp]
    rfl
  have hN : Algebra.norm K.E (y : B.A) ≠ 0 := (y.isUnit.map (Algebra.norm K.E)).ne_zero
  have hmat : (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e' l)) =
      (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)) * Algebra.leftMulMatrix e (y : B.A) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.of_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [he' l]
    conv_lhs => rw [← e.sum_repr ((y : B.A) * e l)]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rw [hspan, SgnBasis.sgnLat_span_basis, ← he, SgnBasis.sgnLat_span_basis, hmat, Matrix.det_mul,
    ← Algebra.norm_eq_matrix_det, Desc.eta_mul (det_trace_ne_zero B hP e) hN, mul_comm]
end GlobalTheory.UnitLemma.Move
