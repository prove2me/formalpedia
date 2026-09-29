-- Prove2me | solution 1 for ModularCurve.apply_mem_regularDifferentials_of_recipe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/13d05c35-aef9-5f95-8547-dd8956dc31a2

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_AlgebraicCurve_dlog_mem_regularDifferentials_of_forall_dvd_ord
import Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_apply_mem_regularDifferentials_of_recipe
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve AlgebraicCurve

theorem solution
    (K : Type*) [Field K] [PerfectField K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] [IsCurveOver K (modularFunctionFieldC K N)] [Algebra.EssFiniteType K (modularFunctionFieldC K N)]
    [∀ w : Place K (modularFunctionFieldC K N), w.DCoordGenerates] [CharP (modularFunctionFieldC K N) p]
    (δ : Pic0.torsion K (modularFunctionFieldC K N) p →+ Ω[↥(modularFunctionFieldC K N)⁄K])
    (hδ : ∀ (y : Pic0.torsion K (modularFunctionFieldC K N) p)
        (E : Divisor.degZero (K := K) (F := modularFunctionFieldC K N)) (g : modularFunctionFieldC K N),
        Pic0.mk E = (y : Pic0 K (modularFunctionFieldC K N)) → g ≠ 0 →
        (∀ v : Place K (modularFunctionFieldC K N),
          (p : ℤ) * (E : Divisor K (modularFunctionFieldC K N)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D K (modularFunctionFieldC K N) g)
    (y : Pic0.torsion K (modularFunctionFieldC K N) p) :
    δ y ∈ regularDifferentials K (modularFunctionFieldC K N) := by
  obtain ⟨E, g, hEy, hg0, hdvd, hord⟩ :=
    Pic0.exists_mk_eq_and_dvd_ord_of_mem_torsion (x := (y : Pic0 K (modularFunctionFieldC K N))) y.2
  rw [hδ y E g hEy hg0 (fun v => (hord v).symm)]
  exact dlog_mem_regularDifferentials_of_forall_dvd_ord K (modularFunctionFieldC K N) p hg0 hdvd

end S_ModularCurve_apply_mem_regularDifferentials_of_recipe
end P2MW
export P2MW.S_ModularCurve_apply_mem_regularDifferentials_of_recipe (solution)
