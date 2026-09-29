-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_globalPointsGL_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/33d4ef08-0750-56c4-a788-6483afea2a41

import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_globalPointsGL_mul

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.AdelicVolume
open LanglandsTunnell.CubicInduction
open scoped NNReal
open LanglandsTunnell.CubicInduction.AdelicEpstein

namespace RationalPointsLift

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Ẑˣ" => IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ

private theorem det_globalPointsGL (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ) =
      Units.map (algebraMap ℚ 𝔸).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
  ext
  exact ((algebraMap ℚ 𝔸).map_det (γ : Matrix (Fin 3) (Fin 3) ℚ)).symm

private theorem ideleNorm_det_globalPointsGL (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ)) = 1 := by
  letI : MeasurableSpace 𝔸 := borel 𝔸
  haveI : BorelSpace 𝔸 := ⟨rfl⟩
  rw [det_globalPointsGL, TateGlobal.ideleNorm, AdeleRing.distribHaarChar_algebraMap ℚ]
  simp

private theorem adelicDiag_vecMul (ξ : Fin 3 → ℚ) (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    adelicDiag (Matrix.vecMul ξ (γ : Matrix (Fin 3) (Fin 3) ℚ)) =
      Matrix.vecMul (adelicDiag ξ) ((globalPointsGL 3 (𝓞 ℚ) ℚ γ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) := by
  funext i
  exact (algebraMap ℚ 𝔸).map_vecMul (γ : Matrix (Fin 3) (Fin 3) ℚ) ξ i

private theorem point_globalPointsGL_mul (t : ℝ) (u : Ẑˣ) (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) :
    point t u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) ξ = point t u g (Matrix.vecMul ξ (γ : Matrix (Fin 3) (Fin 3) ℚ)) := by
  funext i
  simp only [point, adelicDiag_vecMul, Matrix.vecMul_vecMul, Units.val_mul]

private theorem vecMul_ne_zero {ξ : Fin 3 → ℚ} (hξ : ξ ≠ 0) (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    Matrix.vecMul ξ (γ : Matrix (Fin 3) (Fin 3) ℚ) ≠ 0 := by
  intro h
  apply hξ
  have h' :=
    congrArg (fun v => Matrix.vecMul v ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) h
  simpa [Matrix.vecMul_vecMul, Matrix.zero_vecMul, Matrix.vecMul_one] using h'

private def vecMulEquiv (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    {ξ : Fin 3 → ℚ // ξ ≠ 0} ≃ {ξ : Fin 3 → ℚ // ξ ≠ 0} where
  toFun ξ := ⟨Matrix.vecMul ξ.1 (γ : Matrix (Fin 3) (Fin 3) ℚ), vecMul_ne_zero ξ.2 γ⟩
  invFun ξ := ⟨Matrix.vecMul ξ.1 ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ),
    vecMul_ne_zero ξ.2 γ⁻¹⟩
  left_inv ξ := by
    ext1
    simp [Matrix.vecMul_vecMul, Matrix.vecMul_one]
  right_inv ξ := by
    ext1
    simp [Matrix.vecMul_vecMul, Matrix.vecMul_one]

private theorem nnnormSum_globalPointsGL_mul (Φ : (Fin 3 → 𝔸) → ℂ) (t : ℝ) (u : Ẑˣ)
    (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) ξ)‖₊ : ENNReal) =
      ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ)‖₊ : ENNReal) := by
  simp only [point_globalPointsGL_mul]
  exact (vecMulEquiv γ).tsum_eq fun ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0} => (‖Φ (point t u g ξ.1)‖₊ : ENNReal)

end RationalPointsLift

open RationalPointsLift LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.AdelicEpstein

theorem solution
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ)]
    (du : MeasureTheory.Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ))
    (Φ : (Fin 3 → NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) → ℂ) (σ : ℝ)
    (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ) :
    epsteinPlus du Φ σ (globalPointsGL 3 (NumberField.RingOfIntegers ℚ) ℚ γ * g) = epsteinPlus du Φ σ g := by
  unfold epsteinPlus
  simp only [nnnormSum_globalPointsGL_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_globalPointsGL,
    one_mul]

end
end S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_globalPointsGL_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_globalPointsGL_mul (solution)
