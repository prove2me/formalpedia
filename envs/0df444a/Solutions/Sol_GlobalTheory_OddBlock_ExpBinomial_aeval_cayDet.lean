-- Prove2me | solution 1 for GlobalTheory.OddBlock.ExpBinomial.aeval_cayDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:08:59.987808+00:00
-- url     : https://prove2.me/submissions/75aa2f21-a9e1-4ad9-b7a2-a2c3d5f5c976

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelliStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOneStatement
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NewtonBoundPosAndNewtonStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SumEqOfIsHomogeneous
import Theorems.Thm_ReciprocityTheory_PGsh_cayDet_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.OddBlock GlobalTheory.OddBlock.ExpBinomial
namespace GlobalTheory.OddBlock.ExpBinomial
theorem _root_.solution (C : Type) [Field C] (l L E n : ℕ) (hl : (l : C) ≠ 0) :
    MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl
      (MvPolynomial.C (-((l : C) ^ E)⁻¹) * MvPolynomial.X j ^ L : MvPolynomial (Fin n × Fin n) C) +
        MvPolynomial.X (Sum.inr j) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C))
      (cayDet n C) =
    MvPolynomial.C ((-((l : C) ^ E)⁻¹) ^ n) *
      (MvPolynomial.map (Int.castRingHom C) (psi l L E n) +
        MvPolynomial.rename Sum.inl (cayDet n C ^ L)) := by
  rw [psi, map_sub, map_pow (MvPolynomial.map _), MvPolynomial.map_rename, cayDet_map,
    map_pow (MvPolynomial.rename _), sub_add_cancel, cayDet, AlgHom.map_det, RingHom.map_det,
    map_pow]
  have := Matrix.det_smul (R := MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C)
    ((MvPolynomial.map (Int.castRingHom C)).mapMatrix
      (Matrix.of fun b c : Fin n => (MvPolynomial.X (Sum.inl (b, c)) ^ L -
    MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) :
      MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℤ))) (MvPolynomial.C (-((l : C) ^ E)⁻¹))
  rw [Fintype.card_fin] at this
  rw [← this]
  congr 1
  ext1 b c
  have h : (MvPolynomial.C (((l : C) ^ E)⁻¹) * MvPolynomial.C ((l : C) ^ E) :
      MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hl), map_one]
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply,
    MvPolynomial.aeval_X, map_mul, map_pow, MvPolynomial.rename_C, MvPolynomial.rename_X,
    Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.of_apply, map_sub, MvPolynomial.map_X,
    MvPolynomial.map_C, smul_eq_mul, map_neg, map_natCast] at h ⊢
  linear_combination (-MvPolynomial.X (Sum.inr (b, c))) * h
end GlobalTheory.OddBlock.ExpBinomial
