-- Prove2me | solution 1 for JHolomorphic.exists_bijective_clm_I_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T10:53:27.947575+00:00
-- url     : https://prove2.me/submissions/3e0a737c-da18-4726-a42f-874adfb1245c

import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace JHolomorphic

open Module

/-- A real `2n`-dimensional space with a linear complex structure `J` is `ℝ`-isomorphic to `ℂⁿ`
by a map carrying multiplication by `i` to `J`. -/
theorem exists_bijective_clm_I_smul_eq_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (hn : Module.finrank ℝ E = 2 * n) (J : E →L[ℝ] E)
    (hJ : J.comp J = -ContinuousLinearMap.id ℝ E) :
    ∃ T : EuclideanSpace ℂ (Fin n) →L[ℝ] E, Function.Bijective T ∧
      ∀ w, T (Complex.I • w) = J (T w) := by
  have hJ' : J * J = -1 := hJ
  let φ : ℂ →ₐ[ℝ] (E →L[ℝ] E) := Complex.liftAux J hJ'
  letI M : Module ℂ E := Module.compHom E φ.toRingHom
  have hsmul : ∀ (c : ℂ) (v : E), c • v = φ c v := fun _ _ => rfl
  haveI : IsScalarTower ℝ ℂ E := ⟨fun r c v => by
    rw [hsmul, hsmul, map_smul]; rfl⟩
  haveI : Module.Finite ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  have hfr : Module.finrank ℂ E = n := by
    have h := Module.finrank_mul_finrank ℝ ℂ E
    rw [Complex.finrank_real_complex, hn] at h
    omega
  have hfr' : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Module.finrank ℂ E := by
    rw [hfr, finrank_euclideanSpace_fin]
  let L : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] E := LinearEquiv.ofFinrankEq _ _ hfr'
  let T₀ : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] E := (L.toLinearMap).restrictScalars ℝ
  refine ⟨LinearMap.toContinuousLinearMap T₀, ?_, ?_⟩
  · exact L.bijective
  · intro w
    change L (Complex.I • w) = J (L w)
    rw [L.map_smul, hsmul]
    simp [φ]

end JHolomorphic

open JHolomorphic

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (hn : Module.finrank ℝ E = 2 * n) (J : E →L[ℝ] E)
    (hJ : J.comp J = -ContinuousLinearMap.id ℝ E) :
    ∃ T : EuclideanSpace ℂ (Fin n) →L[ℝ] E, Function.Bijective T ∧
      ∀ w, T (Complex.I • w) = J (T w) :=
  exists_bijective_clm_I_smul_eq_aux n hn J hJ
