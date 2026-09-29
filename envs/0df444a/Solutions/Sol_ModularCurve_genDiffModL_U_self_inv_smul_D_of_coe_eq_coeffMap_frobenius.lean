-- Prove2me | solution 1 for ModularCurve.genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e06b342d-0067-5db6-b2f4-420bb89a13f4

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius

set_option autoImplicit false

theorem solution
    (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (S : Set ℕ) [CharP K p]
    (hC : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
      ∃ C : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K],
        ModularCurve.IsFrobPushDiff K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p C)
    (hinj : Function.Injective (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))))
    (f f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hf' : ((f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) =
      ModularCurve.coeffMap (frobenius K p) ((f : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K)) :
    ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM)
        (f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) f) =
      f'⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) f' := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [ModularCurve.genDiffModL_U_self]
  apply hinj
  rw [ModularCurve.isFrobPushDiff_frobPushDiffModL hC, ModularCurve.diffQExp_smul_D,
    ModularCurve.diffQExp_smul_D]
  have hcoe : (((f⁻¹ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) = ((f : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K)⁻¹ :=
    map_inv₀ (IntermediateField.val _) f
  have hcoe' : (((f'⁻¹ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) = ((f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K)⁻¹ :=
    map_inv₀ (IntermediateField.val _) f'
  rw [hcoe, hcoe', hf']
  exact ModularCurve.qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius K p _

end S_ModularCurve_genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius
end P2MW
export P2MW.S_ModularCurve_genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius (solution)
