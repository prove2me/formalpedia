-- Prove2me | solution 1 for NumberField.TateGlobal.ideleNorm_uniformizerIdele
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/703b65a7-33ce-5322-b2ea-b9eb6304e223

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_uniformizerIdele
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal

private theorem norm_coe_uniformizerUnit (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ‖(uniformizerUnit F v : v.adicCompletion F)‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [WithZero.exp, WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv,
    NNReal.coe_natCast]

private theorem norm_one_apply_pow_mult (F : Type) [Field F] [NumberField F]
    (w : InfinitePlace F) : ‖(1 : InfiniteAdeleRing F) w‖ ^ w.mult = 1 := by
  rw [show (1 : InfiniteAdeleRing F) w = 1 from rfl, norm_one, one_pow]

theorem solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  have hfst : (uniformizerIdele F v : AdeleRing (𝓞 F) F).1 = 1 := rfl
  have hself : (uniformizerIdele F v : AdeleRing (𝓞 F) F).2 v
      = (uniformizerUnit F v : v.adicCompletion F) :=
    localUnit_apply_self (𝓞 F) F v (uniformizerUnit F v)
  have hne : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      (uniformizerIdele F v : AdeleRing (𝓞 F) F).2 w = 1 :=
    fun w hw => localUnit_apply_of_ne (𝓞 F) F v (uniformizerUnit F v) hw
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, hfst,
    Finset.prod_eq_one (fun w _ => norm_one_apply_pow_mult F w), one_mul,
    finprod_eq_single _ v (fun w hw => by simp only [hne w hw, norm_one]), hself,
    norm_coe_uniformizerUnit]

end S_NumberField_TateGlobal_ideleNorm_uniformizerIdele
end P2MW
export P2MW.S_NumberField_TateGlobal_ideleNorm_uniformizerIdele (solution)
