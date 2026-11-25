-- Prove2me | solution 1 for GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:37.934482+00:00
-- url     : https://prove2.me/submissions/5860683e-be1d-4e91-8fde-5b96df55d963

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsConductorMulMemAdjoinOfSeparable
import Theorems.Thm_GlobalTheory_DiscConductor_det_smul_eq_sum
import Theorems.Thm_GlobalTheory_DiscConductor_isIntegral_trace_of_isIntegral
import Theorems.Thm_GlobalTheory_UnitLemma_TraceNondeg_eq_zero_of_trace_mul_eq_zero
import Theorems.Thm_GlobalTheory_UnitLemma_exists_basis_pow_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
namespace GlobalTheory.UnitLemma
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsIntegral K.O B.g →
    ∃ c : K.O, c ≠ 0 ∧ ∀ u : B.A, IsIntegral K.O u →
      algebraMap K.O B.A c * u ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
  intro K B hP hg
  classical
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hP
  have hint : ∀ x : B.A, IsIntegral K.O x →
      ∃ t : K.O, algebraMap K.O K.E t = Algebra.trace K.E B.A x := fun x hx =>
    IsIntegrallyClosed.isIntegral_iff.1
      (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral K.O K.E B.A x hx)
  have he_int : ∀ i, IsIntegral K.O (e i) := fun i => by rw [he]; exact hg.pow _
  have hG : ∀ i j, ∃ t : K.O, algebraMap K.O K.E t = Algebra.trace K.E B.A (e i * e j) :=
    fun i j => hint _ ((he_int i).mul (he_int j))
  choose t ht using hG
  let c : K.O := (Matrix.of t).det
  have hc : algebraMap K.O K.E c = (Algebra.traceMatrix K.E e).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [ht, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have hgen : ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by
    intro a
    refine ⟨∑ i : Fin (Module.finrank K.E B.A), monomial (i : ℕ) (e.repr a i), ?_⟩
    calc a = ∑ i, e.repr a i • e i := (e.sum_repr a).symm
      _ = _ := by simp [map_sum, aeval_monomial, he, Algebra.smul_def]
  have hdet : (Algebra.traceMatrix K.E e).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have hwv : e.equivFun (∑ j, v j • e j) = v := by
      rw [← e.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    have hti : ∀ i, Algebra.trace K.E B.A ((∑ j, v j • e j) * e i) = 0 := by
      intro i
      have := congrFun (Algebra.traceMatrix_of_basis_mulVec e (∑ j, v j • e j)) i
      rw [hwv, hv] at this
      exact this.symm
    have hw := GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP hgen
      (∑ j, v j • e j) (fun y => by
        rw [← e.sum_repr y, Finset.mul_sum, map_sum]
        simp [mul_smul_comm, hti])
    exact funext (Fintype.linearIndependent_iff.1 e.linearIndependent v hw)
  refine ⟨c, fun h0 => hdet (by rw [← hc, h0, map_zero]), fun u hu => ?_⟩
  obtain ⟨w, hw⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum K.O K.E B.A _ e u
    (fun i j => ⟨_, ht i j⟩) (fun i => hint _ (hu.mul (he_int i)))
  have h1 : algebraMap K.O B.A c * u = ∑ j, w j • B.g ^ (j : ℕ) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, ← Algebra.smul_def, hc, hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [algebraMap_smul, he]
  rw [h1]
  exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _) _
end GlobalTheory.UnitLemma
