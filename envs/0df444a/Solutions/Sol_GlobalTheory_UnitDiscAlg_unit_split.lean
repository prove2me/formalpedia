-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.unit_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:59:06.341109+00:00
-- url     : https://prove2.me/submissions/20c7708d-03eb-44cc-a8cb-c6408b20154e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewtonStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecomposeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommutantValuationDecompositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuotientIntegralUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitDiscriminantMatrixQuotientIsUnit
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_T_commuting_integral_matrix_decompose
import Theorems.Thm_GlobalTheory_T_exists_integral_idempotent_lift_newton
import Theorems.Thm_GlobalTheory_T_norm_det_le_one_of_entries_norm_le_one
import Theorems.Thm_GlobalTheory_T_ultrametric_norm_det_one_add_smul
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_add
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_mul
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_one
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitDiscAlg
namespace GlobalTheory.UnitDiscAlg
theorem _root_.solution {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] {n : ℕ} {N : Matrix (Fin n) (Fin n) E} {ϖ : E}
    (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hB : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1) (hϖ : ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖)
    (hcomm : ∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x)
    (y : Matrix (Fin n) (Fin n) E) (hyN : y * N = N * y) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧
      e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a := by
  obtain ⟨x, z, a₁, a₂, a₃, ⟨hxN, hzN, h1N, h2N, h3N⟩, hint, hx, hyx, hyz⟩ :=
    GlobalTheory.T.commuting_integral_matrix_decompose E n N ϖ hN hB h0 h1 hϖ y hyN hy
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  obtain ⟨e, a', heN, ha'N, he, heI, ha'I, hea⟩ :=
    GlobalTheory.T.exists_integral_idempotent_lift_newton E n N x a₁ ϖ h1 hxN (fun i j => (hint i j).1) (fun i j => (hint i j).2.2.1) hx
  have hzI : ∀ i j, ‖z i j‖ ≤ 1 := fun i j => (hint i j).2.1
  have ha₂I : ∀ i j, ‖a₂ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.1
  have ha₃I : ∀ i j, ‖a₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.2
  refine ⟨e, a₂ - y * a', heN, ?_, fun i j => ⟨heI i j, integ_sub ha₂I (integ_mul hy ha'I) i j⟩,
    he, ?_, ?_⟩
  · rw [sub_mul, mul_sub, h2N, Matrix.mul_assoc, ha'N, ← Matrix.mul_assoc, hyN, Matrix.mul_assoc]
  ·
    have hye : y * e = e * y := hcomm y e hyN heN
    have hze : z * e = e * z := hcomm z e hzN heN
    have hyz' : y * z = z * y := hcomm y z hyN hzN
    have hprod : (y * e + (1 - e)) * (z * e + (1 - e)) = 1 + ϖ • (a₃ + y * z * a' - a') := by
      have e1 : e = x + ϖ • a' := by rw [← hea]; abel
      have e2 : y * z * x = x + ϖ • a₃ := by rw [← hyz]; abel
      have key : (y * e + (1 - e)) * (z * e + (1 - e)) = 1 + y * z * e - e := by
        have : (y * e + (1 - e)) * (z * e + (1 - e)) =
            y * (e * z) * e + y * e * (1 - e) + (1 - e) * z * e + (1 - e) * (1 - e) := by
          noncomm_ring
        rw [this, ← hze]
        have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
        have hee' : (1 - e) * z * e = 0 := by
          rw [Matrix.mul_assoc, hze, ← Matrix.mul_assoc, sub_mul, one_mul, he, sub_self,
            Matrix.zero_mul]
        have hee'' : (1 - e) * (1 - e) = 1 - e := by
          rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
        rw [Matrix.mul_assoc y e (1 - e), hee, Matrix.mul_zero, hee', hee'',
          ← Matrix.mul_assoc, Matrix.mul_assoc (y * z) e e, he]
        abel
      rw [key]
      conv_lhs => rw [e1]
      rw [Matrix.mul_add, e2, Matrix.mul_smul]
      simp only [smul_add, smul_sub]
      abel
    have hwI : ∀ i j, ‖(y * e + (1 - e)) i j‖ ≤ 1 :=
      integ_add (integ_mul hy heI) (integ_sub integ_one heI)
    have hw'I : ∀ i j, ‖(z * e + (1 - e)) i j‖ ≤ 1 :=
      integ_add (integ_mul hzI heI) (integ_sub integ_one heI)
    have hd := congrArg (fun m => ‖m.det‖) hprod
    simp only [Matrix.det_mul, norm_mul] at hd
    rw [GlobalTheory.T.ultrametric_norm_det_one_add_smul E n _ ϖ h1 (integ_sub (integ_add ha₃I (integ_mul (integ_mul hy hzI) ha'I)) ha'I)]
      at hd
    have ha := GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one E n _ hwI
    have hb := GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one E n _ hw'I
    nlinarith [norm_nonneg (y * e + (1 - e)).det, norm_nonneg (z * e + (1 - e)).det]
  · have : y * (1 - e) = y * (1 - x) - y * (e - x) := by noncomm_ring
    rw [this, hyx, hea, Matrix.mul_smul, ← smul_sub]
end GlobalTheory.UnitDiscAlg
