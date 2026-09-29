-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.reduceSnd_arithmeticGalois_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/04b71c41-80f7-5627-aef5-9f20fd42f7bb

import Mathlib
import Definitions.Def_ModularCurve_GlueData
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_heckeBetaBar
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem P2MWs12.restrictAlong_semilinearAut_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : SemilinearAut.IntertwinesAlong φ.toRingHom g g') (w : Place K F') :
    (g' • w).restrictAlong φ hφ = g • (w.restrictAlong φ hφ) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact SemilinearAut.restrict_smul (F := F) (g := g) (g' := g') (fun x => hgg' x) w

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.reduceSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = P.reduceSnd V := by
  show P.sp ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V).restrictAlong
      (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
    = P.sp (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
  rw [P2MWs12.restrictAlong_semilinearAut_smul (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
      (g := arithmeticGalois (modularFunctionFieldFull N) σ)
      (g' := arithmeticGalois (modularFunctionFieldFull (N * q)) σ)
      (fun x => arithmeticGalois_smul_heckeBetaBar N q σ x) V]
  exact P.d6_inertia σ hσ _

end S_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul (solution)
