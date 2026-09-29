-- Prove2me | solution 1 for NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/adc2ac2e-9424-5f5f-be87-acede0078c0e

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm
open NumberField.AdelicLevel NumberField.AdeleRing

theorem isUnramifiedCharAt_normPowChar (K : Type) [Field K] [NumberField K] (t : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) : IsUnramifiedCharAt (normPowChar K t) v := by
  intro u hu hu'
  show normPowChar K t (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v u)) = 1
  apply normPowChar_eq_one_of_ideleNorm_eq_one
  apply ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
  · rfl
  · rw [FiniteAdeleRing.mem_unitIdeles_iff]
    have hfp : finitePartUnits (𝓞 K) K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v u))
        = localUnit (𝓞 K) K v u := Units.ext rfl
    rw [hfp]
    refine ⟨fun w => ?_, fun w => ?_⟩
    · by_cases hw : w = v
      · subst hw; rw [localUnit_apply_self]; exact hu
      · rw [localUnit_apply_of_ne _ _ _ _ hw]; exact one_mem _
    · rw [← map_inv]
      by_cases hw : w = v
      · subst hw; rw [localUnit_apply_self]; exact hu'
      · rw [localUnit_apply_of_ne _ _ _ _ hw]; exact one_mem _

open scoped Classical in
theorem solution (K : Type) [Field K] [NumberField K] (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    (if IsUnramifiedCharAt (normPowChar K t) v then ((normPowChar K t (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)
      = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) := by
  rw [if_pos (isUnramifiedCharAt_normPowChar K t v), coe_normPowChar_apply, ideleNorm_uniformizerIdele,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow _ _ ?_, ← Complex.cpow_neg]
  rw [Complex.natCast_arg]
  exact Real.pi_ne_zero.symm

end S_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
end P2MW
export P2MW.S_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg (solution)
