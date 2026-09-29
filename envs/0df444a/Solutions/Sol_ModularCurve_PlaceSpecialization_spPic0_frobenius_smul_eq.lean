-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.spPic0_frobenius_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c514c81b-2cd4-5da1-8b13-fcc2d16116e3

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_spPic0_frobenius_smul_eq

open AlgebraicCurve ModularCurve

theorem solution {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    [IsAlgClosed k] [IsCurveOver k (modularFunctionFieldC k N)]
    (S : PlaceSpecialization A ℓ N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) (x : JZero N) :
    S.spPic0 (σ • x) = frobeniusPushforwardGeomLevelPic0OfIsCurveOver k N data hKr (S.spPic0 x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  obtain ⟨D', hD', h'⟩ := S.spPic0_compat D
  rw [h', frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk, galois_smul_pic0_def,
    SemilinearAut.pic0_smul_mk]
  obtain ⟨D'', hD'', h''⟩ := S.spPic0_compat
    (SemilinearAut.degZeroSMulHom (arithmeticGalois (modularFunctionFieldFull N) σ) D)
  rw [h'']
  congr 1
  refine Subtype.ext ?_
  rw [hD'', coe_frobeniusPushforwardGeomLevelDegZero, hD', SemilinearAut.coe_degZeroSMulHom,
    SemilinearAut.divisor_smul_def, frobeniusPushforwardGeomLevel,
    Finsupp.mapDomain.addMonoidHom_apply, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr ?_
  intro w _
  exact S.d6_frobenius σ hσ w

end S_ModularCurve_PlaceSpecialization_spPic0_frobenius_smul_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_spPic0_frobenius_smul_eq (solution)
