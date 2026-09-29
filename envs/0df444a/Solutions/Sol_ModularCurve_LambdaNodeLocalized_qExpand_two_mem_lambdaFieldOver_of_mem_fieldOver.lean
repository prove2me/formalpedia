-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ed757e56-5601-51b5-9aba-80acef967170

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap qExpand_two_jq_mul_lambdaModC_sq"
p2m_open "ModularCurve"
namespace JLProof

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

theorem qExpand_algebraMap (N : ℕ) [NeZero N] (c : Qb) :
    qExpand Qb N (algebraMap Qb LQ c) = algebraMap Qb LQ c := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

theorem jLambda_Qb :
    qExpand Qb 2 (jqModC Qb) * lambdaModC Qb ^ 2 * (16 * lambdaModC Qb - 1) ^ 2
      = (256 * lambdaModC Qb ^ 2 - 16 * lambdaModC Qb + 1) ^ 3 := by
  have h := congrArg (laurentMap (algebraMap ℚ Qb)) ModularCurve.qExpand_two_jq_mul_lambdaModC_sq
  have hj : laurentMap (algebraMap ℚ Qb) jq = jqModC Qb := by
    rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ Qb)
  have hμ : laurentMap (algebraMap ℚ Qb) (lambdaModC ℚ) = lambdaModC Qb := by
    rw [lambdaModC, lambdaModC, laurentMap_laurentMap]
    exact congrArg (fun g => laurentMap g lambdaInt) (RingHom.ext_int _ _)
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, laurentMap_qExpand, hj, hμ, map_ofNat] using h

theorem jLambda_Qb_q (q : ℕ) [NeZero q] :
    qExpand Qb 2 (jqNModC Qb (1 * q)) * lambdaNModC Qb q ^ 2 * (16 * lambdaNModC Qb q - 1) ^ 2
      = (256 * lambdaNModC Qb q ^ 2 - 16 * lambdaNModC Qb q + 1) ^ 3 := by
  have h := congrArg (qExpand Qb q) (jLambda_Qb)
  have hj : qExpand Qb q (qExpand Qb 2 (jqModC Qb)) = qExpand Qb 2 (jqNModC Qb (1 * q)) := by
    rw [jqNModC, qExpand_qExpand, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hj, lambdaNModC] using h

theorem mem_of_jRel (Λ : Subfield LQ) (J m : LQ) (hm : m ∈ Λ)
    (hJ : J * m ^ 2 * (16 * m - 1) ^ 2 = (256 * m ^ 2 - 16 * m + 1) ^ 3) : J ∈ Λ := by
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hJ
    norm_num at hJ
  have h16 : 16 * m - 1 ≠ 0 := by
    intro h0
    have h1 : (256 * m ^ 2 - 16 * m + 1) = 1 := by linear_combination (16 * m) * h0
    rw [h0, h1] at hJ
    norm_num at hJ
  have hD : m ^ 2 * (16 * m - 1) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hm0) (pow_ne_zero _ h16)
  have hJeq : J = (256 * m ^ 2 - 16 * m + 1) ^ 3 / (m ^ 2 * (16 * m - 1) ^ 2) := by
    rw [eq_div_iff hD, ← hJ]; ring
  rw [hJeq]
  have h16m : (16 : LQ) ∈ Λ := by exact_mod_cast natCast_mem Λ 16
  have h256m : (256 : LQ) ∈ Λ := by exact_mod_cast natCast_mem Λ 256
  refine div_mem (pow_mem (add_mem (sub_mem (mul_mem h256m (pow_mem hm 2)) (mul_mem h16m hm)) (one_mem _)) 3)
    (mul_mem (pow_mem hm 2) (pow_mem (sub_mem (mul_mem h16m hm) (one_mem _)) 2))

end JLProof
end ModularCurve

end

open ModularCurve.JLProof in

theorem solution
    (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ fieldOver (1 * q) K) :
    qExpand (AlgebraicClosure ℚ) 2 x ∈ lambdaFieldOver q K := by

  suffices h : fieldOver (1 * q) K ≤ (lambdaFieldOver q K).comap (qExpand (AlgebraicClosure ℚ) 2) from h hx
  unfold fieldOver
  rw [Subfield.closure_le]
  rintro z (⟨c, rfl⟩ | rfl | rfl)
  ·
    show qExpand (AlgebraicClosure ℚ) 2 (CharPReduction.constSeries _ c) ∈ lambdaFieldOver q K
    rw [CharPReduction.constSeries, RingHom.comp_apply, qExpand_algebraMap]
    exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
  ·
    show qExpand (AlgebraicClosure ℚ) 2 (jqModC (AlgebraicClosure ℚ)) ∈ lambdaFieldOver q K
    exact mem_of_jRel (lambdaFieldOver q K) (qExpand (AlgebraicClosure ℚ) 2 (jqModC (AlgebraicClosure ℚ)))
      (lambdaModC (AlgebraicClosure ℚ)) (lambdaModC_mem_lambdaFieldOver q K) jLambda_Qb
  ·
    show qExpand (AlgebraicClosure ℚ) 2 (jqNModC (AlgebraicClosure ℚ) (1 * q)) ∈ lambdaFieldOver q K
    exact mem_of_jRel (lambdaFieldOver q K) (qExpand (AlgebraicClosure ℚ) 2 (jqNModC (AlgebraicClosure ℚ) (1 * q)))
      (lambdaNModC (AlgebraicClosure ℚ) q) (lambdaNModC_mem_lambdaFieldOver q K) (jLambda_Qb_q q)

end S_ModularCurve_LambdaNodeLocalized_qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver (solution)
