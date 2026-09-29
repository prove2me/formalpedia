-- Prove2me | solution 1 for ModularCurve.thetaL_jqModC_mul_intSeriesC_X_mul_dedekindEtaUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/53f7d6f0-f61f-50ff-9c3e-f9a984fded85

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_thetaL_jq_mul_deltaSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_thetaL_jqModC_mul_intSeriesC_X_mul_dedekindEtaUnit
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve HahnSeries

namespace ThetaJDelta

noncomputable def thetaZ (x : LaurentSeries ℤ) : LaurentSeries ℤ :=
  single (1 : ℤ) (1 : ℤ) * LaurentSeries.derivative ℤ x

theorem map_coeff' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) (n : ℤ) :
    (x.map f).coeff n = f (x.coeff n) := rfl

theorem map_mul' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x y : LaurentSeries R) :
    (x * y).map f = x.map f * y.map f :=
  HahnSeries.map_mul f.toNonUnitalRingHom

theorem map_neg' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) :
    (-x).map f = -(x.map f) :=
  HahnSeries.map_neg f.toAddMonoidHom

theorem map_derivative {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) :
    (LaurentSeries.derivative R x).map f = LaurentSeries.derivative S (x.map f) := by
  ext n
  rw [map_coeff', LaurentSeries.derivative_apply, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    LaurentSeries.hasseDeriv_coeff, map_zsmul, map_coeff']

theorem map_single_one_one {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (single (1 : ℤ) (1 : R)).map f = single (1 : ℤ) (1 : S) := by
  ext n
  rw [map_coeff']
  by_cases h : n = 1
  · subst h; rw [coeff_single_same, coeff_single_same, map_one]
  · rw [coeff_single_of_ne h, coeff_single_of_ne h, map_zero]

theorem map_thetaZ (L : Type*) [Field L] (f : ℤ →+* L) (x : LaurentSeries ℤ) :
    (thetaZ x).map f = thetaL L (x.map f) := by
  rw [thetaZ, map_mul', map_single_one_one, map_derivative, thetaL_apply]

theorem ofPowerSeries_coeff_neg {R : Type*} [CommRing R] (q : PowerSeries R) (n : ℤ) (hn : n < 0) :
    (ofPowerSeries ℤ R q).coeff n = 0 := by
  rw [ofPowerSeries_apply, embDomain_notin_range]
  rintro ⟨m, hm⟩
  first
    | (simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Nat.castOrderEmbedding_apply] at hm; omega)
    | (simp at hm; omega)
    | omega

theorem map_ofPowerSeries {S : Type*} [CommRing S] (f : ℤ →+* S) (p : PowerSeries ℤ) :
    (ofPowerSeries ℤ ℤ p).map f = ofPowerSeries ℤ S (p.map f) := by
  ext n
  rw [map_coeff']
  rcases lt_or_ge n 0 with hn | hn
  · rw [ofPowerSeries_coeff_neg _ _ hn, ofPowerSeries_coeff_neg _ _ hn, map_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

theorem map_injective_rat {x y : LaurentSeries ℤ} (h : x.map (Int.castRingHom ℚ) = y.map (Int.castRingHom ℚ)) :
    x = y := by
  ext n
  have := congrArg (fun z : LaurentSeries ℚ => z.coeff n) h
  simp only [map_coeff', eq_intCast, Int.cast_inj] at this
  exact this

theorem intSeriesC_eq_map (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intSeriesC K p = (ofPowerSeries ℤ ℤ p).map (Int.castRingHom K) := by
  rw [map_ofPowerSeries]; rfl

theorem thetaZ_jqModC_mul_delta :
    thetaZ (jqModC ℤ) * ofPowerSeries ℤ ℤ (PowerSeries.X * dedekindEtaUnit) =
      -ofPowerSeries ℤ ℤ (eisenstein4 ^ 2 * eisenstein6) := by
  apply map_injective_rat
  rw [map_mul', map_thetaZ, ← jqModC_eq_map_intCast, jqModC_rat, map_ofPowerSeries, map_neg', map_ofPowerSeries]
  have hδ : ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X * dedekindEtaUnit)) = deltaSeries := by
    rw [map_mul, PowerSeries.map_X, map_mul, ofPowerSeries_X]
    rfl
  rw [hδ]
  exact ModularCurve.thetaL_jq_mul_deltaSeries

end ThetaJDelta

theorem solution (K : Type*) [Field K] :
    thetaL K (jqModC K) * intSeriesC K (PowerSeries.X * dedekindEtaUnit) =
      -intSeriesC K (eisenstein4 ^ 2 * eisenstein6) := by
  rw [ThetaJDelta.intSeriesC_eq_map, ThetaJDelta.intSeriesC_eq_map, jqModC_eq_map_intCast (K := K),
    ← ThetaJDelta.map_thetaZ, ← ThetaJDelta.map_mul', ThetaJDelta.thetaZ_jqModC_mul_delta, ThetaJDelta.map_neg']

end S_ModularCurve_thetaL_jqModC_mul_intSeriesC_X_mul_dedekindEtaUnit
end P2MW
export P2MW.S_ModularCurve_thetaL_jqModC_mul_intSeriesC_X_mul_dedekindEtaUnit (solution)
