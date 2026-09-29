-- Prove2me | solution 1 for NumberField.TateGlobal.localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fc0473b5-7dc2-5f2b-b82d-f529365bce08

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

open NumberField.AdelicLevel in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (hχ : IsUnramifiedCharAt χ v)
    (ϖ : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) :
    localChar χ v ϖ = χ (uniformizerIdele K v) := by
  have hϖ₀ : Valued.v ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := valued_uniformizerUnit K v
  have hexp : (↑(Multiplicative.ofAdd (-1 : ℤ)) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) := rfl
  have hne : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.coe_ne_zero
  have hu : Valued.v (((ϖ * (uniformizerUnit K v)⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hϖ, hϖ₀, hexp]
    exact mul_inv_cancel₀ hne
  have hu' : Valued.v (((ϖ * (uniformizerUnit K v)⁻¹)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have h1 : localChar χ v (ϖ * (uniformizerUnit K v)⁻¹) = 1 :=
    hχ _ (by rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hu])
      (by rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hu'])
  calc localChar χ v ϖ = localChar χ v ((ϖ * (uniformizerUnit K v)⁻¹) * uniformizerUnit K v) := by
        rw [inv_mul_cancel_right]
    _ = localChar χ v (ϖ * (uniformizerUnit K v)⁻¹) * localChar χ v (uniformizerUnit K v) := map_mul _ _ _
    _ = localChar χ v (uniformizerUnit K v) := by rw [h1, one_mul]
    _ = χ (uniformizerIdele K v) := rfl

end S_NumberField_TateGlobal_localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt
end P2MW
export P2MW.S_NumberField_TateGlobal_localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt (solution)
