-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.spPic0_inertia_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1238fa2b-ac9a-5a63-a62d-c052a68b8861

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_spPic0_inertia_smul

open AlgebraicCurve ModularCurve

theorem solution {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    (S : PlaceSpecialization A ℓ N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : JZero N) : S.spPic0 (σ • x) = S.spPic0 x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk]
  obtain ⟨D₁, hD₁, h₁⟩ := S.spPic0_compat (SemilinearAut.degZeroSMulHom (arithmeticGalois (modularFunctionFieldFull N) σ) D)
  obtain ⟨D₂, hD₂, h₂⟩ := S.spPic0_compat D
  rw [h₁, h₂]
  congr 1
  refine Subtype.ext ?_
  rw [hD₁, hD₂, SemilinearAut.coe_degZeroSMulHom, SemilinearAut.divisor_smul_def,
    ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr ?_
  intro w _
  exact S.d6_inertia σ hσ w

end S_ModularCurve_PlaceSpecialization_spPic0_inertia_smul
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_spPic0_inertia_smul (solution)
