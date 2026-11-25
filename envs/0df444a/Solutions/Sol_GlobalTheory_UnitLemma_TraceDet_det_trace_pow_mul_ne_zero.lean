-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:06.158846+00:00
-- url     : https://prove2.me/submissions/fbb4d185-ade5-4bee-b124-dde580892af9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTracePowAddMulUnitNeZero
import Theorems.Thm_GlobalTheory_T_exists_power_basis_of_charpoly_separable
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_eq_zero_of_trace_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TraceDet
namespace GlobalTheory.UnitLemma.TraceDet
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ u : B.A, IsUnit u →
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ ((k : ℕ) + (l : ℕ)) * u)).det ≠ 0 := by
  intro K B hsep u hu hdet
  classical
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_power_basis_of_charpoly_separable K B hsep
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  set w : B.A := ∑ l, v l • e l with hw
  have hk : ∀ k, Algebra.trace K.E B.A ((w * u) * e k) = 0 := by
    intro k
    have := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this, hw, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul, he, he, pow_add]
    rw [mul_comm (v l)]
    congr 1
    congr 1
    ring
  have hz : w * u = 0 := by
    apply GlobalTheory.UnitLemma.Centraliser.eq_zero_of_trace_mul B hsep
    intro y
    rw [← e.sum_repr y, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, map_smul, hk k, smul_zero]
  have hw0 : w = 0 := (hu.mul_left_eq_zero).1 hz
  apply hv0
  exact (Fintype.linearIndependent_iff.1 e.linearIndependent) v hw0 |> funext
end GlobalTheory.UnitLemma.TraceDet
