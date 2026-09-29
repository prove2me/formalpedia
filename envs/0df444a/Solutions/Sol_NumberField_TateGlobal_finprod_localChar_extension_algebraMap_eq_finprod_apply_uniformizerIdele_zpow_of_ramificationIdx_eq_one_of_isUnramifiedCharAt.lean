-- Prove2me | solution 1 for NumberField.TateGlobal.finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1fd2b6b2-925b-5d2b-bc73-96853a00a473

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm

namespace P2mTransport

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizerUnit_zpow (n : ℤ) :
    Valued.v (((uniformizerUnit K w) ^ n : (w.adicCompletion K)ˣ) : w.adicCompletion K) = WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem localChar_eq_zpow_of_isUnramifiedCharAt (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : IsUnramifiedCharAt μ w) (y : (w.adicCompletion K)ˣ) (n : ℤ)
    (hy : Valued.v (y : w.adicCompletion K) = WithZero.exp n) :
    localChar μ w y = (μ (uniformizerIdele K w)) ^ (-n) := by
  have hu : Valued.v ((y * (uniformizerUnit K w) ^ n : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1 := by
    rw [Units.val_mul, map_mul, hy, valued_uniformizerUnit_zpow, ← WithZero.exp_add]
    simp
  have h1 : localChar μ w (y * (uniformizerUnit K w) ^ n) = 1 := by
    refine hμ _ ?_ ?_
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  rw [map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h1
  rw [h1]
  rfl

end P2mTransport

open P2mTransport in
theorem solution
    (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [Algebra E K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 E))
    (he : ∀ w : v.Extension (𝓞 K), Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1)
    (hμ : ∀ w : v.Extension (𝓞 K), IsUnramifiedCharAt μ w.1)
    (x : (v.adicCompletion E)ˣ) (n : ℤ)
    (hx : Valued.v (x : v.adicCompletion E) = WithZero.exp n) :
    (∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
        (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)).toMonoidHom x) : ℂˣ) : ℂ)) =
      (∏ᶠ w : v.Extension (𝓞 K), ((μ (uniformizerIdele K w.1) : ℂˣ) : ℂ)) ^ (-n) := by
  classical
  haveI : Fintype (v.Extension (𝓞 K)) := HeightOneSpectrum.Extension.fintype (𝓞 E) E K (𝓞 K) v

  have hw : ∀ w : v.Extension (𝓞 K),
      localChar μ w.1 (Units.map (algebraMap (v.adicCompletion E) (w.1.adicCompletion K)).toMonoidHom x) =
        (μ (uniformizerIdele K w.1)) ^ (-n) := by
    intro w
    refine localChar_eq_zpow_of_isUnramifiedCharAt K w.1 μ (hμ w) _ n ?_
    show Valued.v ((w.adicCompletionSemialgHom E K) (x : v.adicCompletion E)) = WithZero.exp n
    rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom E K w, hx]
    have hew : (w.1.under (𝓞 E)).asIdeal.ramificationIdx' w.1.asIdeal = 1 := by
      rw [w.2]
      exact he w
    rw [hew, pow_one]
  simp_rw [hw, Units.val_zpow_eq_zpow_val]
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, Finset.prod_zpow]

end S_NumberField_TateGlobal_finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt
end P2MW
export P2MW.S_NumberField_TateGlobal_finprod_localChar_extension_algebraMap_eq_finprod_apply_uniformizerIdele_zpow_of_ramificationIdx_eq_one_of_isUnramifiedCharAt (solution)
