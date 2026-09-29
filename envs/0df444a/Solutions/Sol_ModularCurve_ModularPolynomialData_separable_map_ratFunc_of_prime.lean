-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/635195cd-0458-5f41-9db9-8da81c6c4d35

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_jqModC_of_prime
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData jqModC ModularPolynomialData.separable_map_jqModC_of_prime transcendental_jqModC"
p2m_open "ModularCurve"
namespace Zeta
open Polynomial

theorem separable_map_ratFunc_of_transcendental {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (hx : Transcendental F x) (P : Polynomial (Polynomial F))
    (h : (P.map (Polynomial.aeval x).toRingHom).Separable) :
    (P.map (algebraMap (Polynomial F) (RatFunc F))).Separable := by
  have hinj : Function.Injective (Polynomial.aeval (R := F) x).toRingHom :=
    fun a b hab => (transcendental_iff_injective.mp hx) hab
  let θ : RatFunc F →+* E := IsFractionRing.lift hinj
  have hθ : θ.comp (algebraMap (Polynomial F) (RatFunc F)) = (Polynomial.aeval x).toRingHom :=
    RingHom.ext fun p => IsFractionRing.lift_algebraMap hinj p
  rw [← Polynomial.separable_map θ, Polynomial.map_map, hθ]
  exact h

theorem map_aeval_comp_mapRingHom_intCast {K E : Type*} [Field K] [CommRing E] [Algebra K E] (x : E)
    (Φ : Polynomial (Polynomial ℤ)) :
    (Φ.map (mapRingHom (Int.castRingHom K))).map (Polynomial.aeval x).toRingHom
      = Φ.map (eval₂RingHom (Int.castRingHom E) x) := by
  rw [Polynomial.map_map]
  refine congrArg (fun f : Polynomial ℤ →+* E => Φ.map f) ?_
  exact Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

theorem natCast_ne_zero_algClosure_zmod (ℓ N : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    (N : AlgebraicClosure (ZMod ℓ)) ≠ 0 := by
  haveI : CharP (AlgebraicClosure (ZMod ℓ)) ℓ :=
    charP_of_injective_algebraMap (algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))).injective ℓ
  intro h
  exact hℓ ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod ℓ)) ℓ N).mp h)

theorem separable_map_ratFunc_of_prime (K : Type*) [Field K] (N : ℕ) [Fact N.Prime]
    (data : ModularCurve.ModularPolynomialData N) (hNK : (N : K) ≠ 0) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable := by
  apply separable_map_ratFunc_of_transcendental (jqModC K) (ModularCurve.transcendental_jqModC K)
  rw [map_aeval_comp_mapRingHom_intCast]
  exact ModularCurve.ModularPolynomialData.separable_map_jqModC_of_prime K data hNK

theorem separable_map_ratFunc_of_prime_of_not_dvd (N : ℕ) [Fact N.Prime] (data : ModularCurve.ModularPolynomialData N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (AlgebraicClosure (ZMod ℓ))))).map
      (algebraMap (Polynomial (AlgebraicClosure (ZMod ℓ))) (RatFunc (AlgebraicClosure (ZMod ℓ))))).Separable :=
  separable_map_ratFunc_of_prime (AlgebraicClosure (ZMod ℓ)) N data (natCast_ne_zero_algClosure_zmod ℓ N hℓ)

end Zeta
end ModularCurve

theorem solution (K : Type*) [Field K] (N : ℕ) [Fact N.Prime] (data : ModularCurve.ModularPolynomialData N)
    (hNK : (N : K) ≠ 0) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable :=
  ModularCurve.Zeta.separable_map_ratFunc_of_prime K N data hNK

end S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime (solution)
