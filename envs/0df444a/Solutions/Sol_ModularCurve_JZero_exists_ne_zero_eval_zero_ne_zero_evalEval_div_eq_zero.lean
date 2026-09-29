-- Prove2me | solution 1 for ModularCurve.JZero.exists_ne_zero_eval_zero_ne_zero_evalEval_div_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a592e308-4bf1-5602-95d4-3970fd81c95a

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Theorems.Thm_Transcendental_exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_ne_zero_eval_zero_ne_zero_evalEval_div_eq_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_exists_ne_zero_eval_zero_ne_zero_evalEval_div_eq_zero.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_JZero_exists_ne_zero_eval_zero_ne_zero_evalEval_div_eq_zero.ModularCurve Polynomial"

namespace ModularCurve p2m_export "ModularCurve" "IsEmbBasis dedekindPsi modularFunctionFieldBar JZero jBar CompEq.finrank_adjoin_jBar_eq_dedekindPsi" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.c22_dedekindPsi_pos (N : ℕ) [NeZero N] : 0 < dedekindPsi N := by
  unfold dedekindPsi
  apply Finset.sum_pos
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.div_pos (Nat.divisor_le hd.1) (Nat.pos_of_mem_divisors hd.1)
  · exact ⟨1, Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩⟩

p2m_open_scoped "AlgebraicCurve" in

theorem AlgebraicCurve.c22_transcendental_of_not_mem_range {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] {z : F} (hz : z ∉ Set.range (algebraMap K F)) : Transcendental K z := by
  intro halg
  exact hz (minpoly.mem_range_of_degree_eq_one K z
    (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral)))

p2m_open_scoped "AlgebraicCurve" in

theorem AlgebraicCurve.c22_exists_ne_zero_eval_zero_ne_zero_evalEval_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (z h : F) (hh : h ≠ 0) :
    ∃ H : Polynomial (Polynomial K), H ≠ 0 ∧ H.eval 0 ≠ 0 ∧
      (H.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z h = 0 := by
  classical
  by_cases hz : z ∈ Set.range (algebraMap K F)
  · obtain ⟨c, hc⟩ := hz
    refine ⟨C (X - C c), C_ne_zero.mpr (X_sub_C_ne_zero c), ?_, ?_⟩
    · rw [eval_C]
      exact X_sub_C_ne_zero c
    · rw [Polynomial.map_C, evalEval_C, coe_mapRingHom, Polynomial.map_sub, map_X, map_C, eval_sub,
        eval_X, eval_C, ← hc, sub_self]
  · have hzt : Transcendental K z := AlgebraicCurve.c22_transcendental_of_not_mem_range hz
    obtain ⟨G, hGirr, hG0, -⟩ :=
      Transcendental.exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero x₀ hzt h
    refine ⟨G, hGirr.ne_zero, ?_, hG0⟩
    intro h0
    have hdvd : (X : Polynomial (Polynomial K)) ∣ G := X_dvd_iff.mpr (by rwa [coeff_zero_eq_eval_zero])
    obtain ⟨Q, hQ⟩ := hdvd
    have hQu : IsUnit Q := (hGirr.isUnit_or_isUnit hQ).resolve_left Polynomial.not_isUnit_X
    obtain ⟨q, hq, hqC⟩ := Polynomial.isUnit_iff.mp hQu
    obtain ⟨c, hc, hcC⟩ := Polynomial.isUnit_iff.mp hq
    apply hh
    have hrel := hG0
    rw [hQ, ← hqC, ← hcC, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, coe_mapRingHom,
      Polynomial.map_C, evalEval_mul, evalEval_X, evalEval_C, eval_C] at hrel
    exact (mul_eq_zero.mp hrel).resolve_right ((map_ne_zero (algebraMap K F)).mpr hc.ne_zero)

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (h : modularFunctionFieldBar N) (hh : h ≠ 0) (i l : Fin r) :
    ∃ H : Polynomial (Polynomial (AlgebraicClosure ℚ)), H ≠ 0 ∧ H.eval 0 ≠ 0 ∧
      (H.map (Polynomial.mapRingHom (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))).evalEval
        (s l * (s i)⁻¹) h = 0 := by
  haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) :=
    Module.finite_of_finrank_pos
      (by rw [ModularCurve.CompEq.finrank_adjoin_jBar_eq_dedekindPsi N]; exact ModularCurve.c22_dedekindPsi_pos N)
  exact AlgebraicCurve.c22_exists_ne_zero_eval_zero_ne_zero_evalEval_eq_zero (jBar N) _ h hh

#print axioms solution

end S_ModularCurve_JZero_exists_ne_zero_eval_zero_ne_zero_evalEval_div_eq_zero
end P2MW
export P2MW.S_ModularCurve_JZero_exists_ne_zero_eval_zero_ne_zero_evalEval_div_eq_zero (solution)
