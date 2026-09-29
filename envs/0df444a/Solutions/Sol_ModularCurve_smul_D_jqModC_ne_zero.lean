-- Prove2me | solution 1 for ModularCurve.smul_D_jqModC_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b84ea46d-51ac-54dc-b7a3-a56e7da72e46

import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_smul_D_jqModC_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

open AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "qSeriesBar qInftyPlaceBar jqModC modularFunctionFieldC jqModC_mem order_jqModC ord_qInftyPlaceBar"
p2m_open "ModularCurve"

section NE

variable (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ]

private noncomputable abbrev jBarC : modularFunctionFieldC K ℓ := ⟨jqModC K, jqModC_mem K ℓ⟩

private theorem order_qSeriesBar_jBarC :
    (qSeriesBar K (modularFunctionFieldC K ℓ) (jBarC K ℓ)).order = -1 :=
  order_jqModC K

private noncomputable abbrev vOne : Place K (modularFunctionFieldC K ℓ) :=
  qInftyPlaceBar K (modularFunctionFieldC K ℓ) ⟨jBarC K ℓ, order_qSeriesBar_jBarC K ℓ⟩

private theorem ord_vOne_jBarC : (vOne K ℓ).ord (jBarC K ℓ) = -1 := by
  rw [ord_qInftyPlaceBar, order_qSeriesBar_jBarC]

private theorem ord_vOne_jBarC_inv : (vOne K ℓ).ord (jBarC K ℓ)⁻¹ = 1 := by
  rw [Place.ord_inv, ord_vOne_jBarC]; norm_num

variable {K ℓ}

private theorem D_jBarC_ne_zero [PerfectField K] (x₀ : modularFunctionFieldC K ℓ)
    [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set (modularFunctionFieldC K ℓ))) (modularFunctionFieldC K ℓ)] :
    KaehlerDifferential.D K (modularFunctionFieldC K ℓ) (jBarC K ℓ) ≠ 0 := by
  intro h
  apply (vOne K ℓ).D_ne_zero_of_ord_eq_one x₀ (ord_vOne_jBarC_inv K ℓ)
  rw [Derivation.leibniz_inv, h, smul_zero]

private theorem smul_D_jBarC_ne_zero [PerfectField K] (x₀ : modularFunctionFieldC K ℓ)
    [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set (modularFunctionFieldC K ℓ))) (modularFunctionFieldC K ℓ)]
    {z : modularFunctionFieldC K ℓ} (hz : z ≠ 0) :
    z • KaehlerDifferential.D K (modularFunctionFieldC K ℓ) (jBarC K ℓ) ≠ 0 :=
  smul_ne_zero hz (D_jBarC_ne_zero x₀)

end NE

end ModularCurve

theorem solution {K : Type*} [Field K] {ℓ : ℕ} [NeZero ℓ]
    [PerfectField K] (x₀ : ModularCurve.modularFunctionFieldC K ℓ)
    [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set (ModularCurve.modularFunctionFieldC K ℓ)))
      (ModularCurve.modularFunctionFieldC K ℓ)]
    {z : ModularCurve.modularFunctionFieldC K ℓ} (hz : z ≠ 0) :
    z • KaehlerDifferential.D K (ModularCurve.modularFunctionFieldC K ℓ)
      ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K ℓ⟩ ≠ 0 :=
  ModularCurve.smul_D_jBarC_ne_zero x₀ hz

end S_ModularCurve_smul_D_jqModC_ne_zero
end P2MW
export P2MW.S_ModularCurve_smul_D_jqModC_ne_zero (solution)
