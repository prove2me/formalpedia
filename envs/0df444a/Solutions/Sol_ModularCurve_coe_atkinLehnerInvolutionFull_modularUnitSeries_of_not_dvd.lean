-- Prove2me | solution 1 for ModularCurve.coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/45eb7585-ef19-59e3-91b6-8626dcce716c

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_modularFunctionFieldFull_algHom_ext
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField AlgebraicCurve

namespace LigozatUnitAL

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

def incl : modularFunctionFieldFull p →+* modularFunctionFieldFull (N * p) where
  toFun x := ⟨x.1, full_degeneracy_le (dvd_mul_left p N) x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem incl_apply (x : modularFunctionFieldFull p) :
    incl N p x = ⟨x.1, full_degeneracy_le (dvd_mul_left p N) x.2⟩ := rfl

theorem coe_incl (x : modularFunctionFieldFull p) :
    ((incl N p x : modularFunctionFieldFull (N * p)) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) := by
  rw [incl_apply]

theorem atkinLehner_comp_incl (hpN : ¬ p ∣ N) :
    (((atkinLehnerInvolutionFull N p : _ →+* _).comp (incl N p)).toRatAlgHom :
        modularFunctionFieldFull p →ₐ[ℚ] modularFunctionFieldFull (N * p))
      = ((incl N p).comp (frickeInvolutionFull p : _ →+* _)).toRatAlgHom := by
  have hσ : IsAtkinLehnerAutFull N p (atkinLehnerInvolutionFull N p) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N p
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N p Fact.out hpN)
  have hτ : IsFrickeAutFull p (frickeInvolutionFull p) :=
    ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime p
  obtain ⟨h1, h2⟩ := hσ 1 inferInstance (one_dvd N)
  have hτ1 := hτ 1 p (one_mul p) inferInstance inferInstance
  have hτ2 := hτ p 1 (mul_one p) inferInstance inferInstance
  refine ModularCurve.modularFunctionFieldFull_algHom_ext fun d hd0 hd => ?_
  rw [RingHom.toRatAlgHom_apply, RingHom.toRatAlgHom_apply, RingHom.comp_apply, RingHom.comp_apply,
    RingHom.coe_coe, RingHom.coe_coe]
  apply Subtype.ext
  rw [coe_incl]
  rcases (Nat.dvd_prime Fact.out).mp hd with rfl | rfl
  ·
    have hel : incl N p (⟨qExpand ℚ 1 jq, jqd_mem_full p hd⟩ : modularFunctionFieldFull p) =
        ⟨qExpand ℚ 1 jq, jqd_mem_full (N * p) (Dvd.dvd.mul_right (one_dvd N) p)⟩ := by
      rw [incl_apply]
    rw [hel, h1, hτ1]
    exact qExpand_congr (one_mul p) jq
  ·
    have hel : incl N d (⟨qExpand ℚ d jq, jqd_mem_full d hd⟩ : modularFunctionFieldFull d) =
        ⟨qExpand ℚ (1 * d) jq, jqd_mem_full (N * d) (Nat.mul_dvd_mul_right (one_dvd N) d)⟩ := by
      rw [incl_apply]; exact Subtype.ext (qExpand_congr (one_mul d).symm jq)
    rw [hel, h2, hτ2]

theorem coe_atkinLehnerInvolutionFull_modularUnitSeries (hpN : ¬ p ∣ N)
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull (N * p)) :
    ((atkinLehnerInvolutionFull N p ⟨modularUnitSeries p, hmem⟩ :
        modularFunctionFieldFull (N * p)) : LaurentSeries ℚ) =
      (p : ℚ) ^ 12 • (modularUnitSeries p)⁻¹ := by
  have hu : modularUnitSeries p ∈ modularFunctionFieldFull p :=
    ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull p
  have key := AlgHom.congr_fun (atkinLehner_comp_incl N p hpN) ⟨modularUnitSeries p, hu⟩
  rw [RingHom.toRatAlgHom_apply, RingHom.toRatAlgHom_apply, RingHom.comp_apply, RingHom.comp_apply,
    RingHom.coe_coe, RingHom.coe_coe] at key
  have hel : incl N p (⟨modularUnitSeries p, hu⟩ : modularFunctionFieldFull p) =
      (⟨modularUnitSeries p, hmem⟩ : modularFunctionFieldFull (N * p)) := by rw [incl_apply]
  rw [hel] at key
  rw [key, coe_incl, ModularCurve.coe_frickeInvolutionFull_modularUnitSeries p hu]

theorem atkinLehnerInvolutionFull_modularUnitSeries (hpN : ¬ p ∣ N)
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull (N * p)) :
    atkinLehnerInvolutionFull N p ⟨modularUnitSeries p, hmem⟩ =
      ((p : ℕ) : modularFunctionFieldFull (N * p)) ^ 12 *
        (⟨modularUnitSeries p, hmem⟩ : modularFunctionFieldFull (N * p))⁻¹ := by
  apply Subtype.ext
  rw [coe_atkinLehnerInvolutionFull_modularUnitSeries N p hpN hmem, MulMemClass.coe_mul,
    SubmonoidClass.coe_pow]
  rw [← HahnSeries.C_mul_eq_smul, map_pow, map_natCast]
  norm_cast

end LigozatUnitAL

end

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (hmem : ModularCurve.modularUnitSeries p ∈ ModularCurve.modularFunctionFieldFull (N * p)) :
    ((ModularCurve.atkinLehnerInvolutionFull N p ⟨ModularCurve.modularUnitSeries p, hmem⟩ :
        ModularCurve.modularFunctionFieldFull (N * p)) : LaurentSeries ℚ) =
      (p : ℚ) ^ 12 • (ModularCurve.modularUnitSeries p)⁻¹ :=
  LigozatUnitAL.coe_atkinLehnerInvolutionFull_modularUnitSeries N p hpN hmem

end S_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd (solution)
