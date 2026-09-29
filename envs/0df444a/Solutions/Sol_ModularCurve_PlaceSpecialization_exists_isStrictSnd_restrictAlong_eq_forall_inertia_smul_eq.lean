-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e9c0e941-7001-5b0b-b099-720cb68659b9

import Definitions.Def_ModularCurve_GlueData
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_heckeBetaBar
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_heckeAlphaBar
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq.AlgebraicCurve ModularCurve"

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place SemilinearAut algebraAlong isScalarTower_along isIntegral_along SemilinearAut.IntertwinesAlong SemilinearAut.restrict_smul" namespace Place p2m_export "AlgebraicCurve.Place" "restrictAlong" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

theorem AlgebraicCurve.Place.restrictAlong_semilinearAut_smul
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
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hu : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp u)) ≠ P.sp u)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull N) σ • u = u) :
    ∃ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictSnd V ∧
        V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = u ∧
        P.reduceSnd V = P.sp u ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V  := by
  obtain ⟨W₀, hβu, hαW, -, huniq⟩ := P.d2 u hu
  refine ⟨W₀, ⟨?_, ?_⟩, hβu, ?_, ?_⟩
  · show P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
        = frobOnPlacesGeomLevel k N data hKr
            (P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ))
    rw [hβu]
    exact hαW
  · show frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
        (P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)))
          ≠ P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
    rw [hβu]
    exact hu
  · show P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) = P.sp u
    rw [hβu]
  · intro σ hσ
    apply huniq
    · rw [Place.restrictAlong_semilinearAut_smul (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
          (g := arithmeticGalois (modularFunctionFieldFull N) σ)
          (g' := arithmeticGalois (modularFunctionFieldFull (N * q)) σ)
          (fun x => arithmeticGalois_smul_heckeBetaBar N q σ x) W₀, hβu]
      exact hfix σ hσ
    · rw [Place.restrictAlong_semilinearAut_smul (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
          (g := arithmeticGalois (modularFunctionFieldFull N) σ)
          (g' := arithmeticGalois (modularFunctionFieldFull (N * q)) σ)
          (fun x => arithmeticGalois_smul_heckeAlphaBar N q σ x) W₀, P.d6_inertia σ hσ, hαW]

end S_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq (solution)
