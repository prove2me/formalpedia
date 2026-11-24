-- Prove2me | solution 1 for GlobalTheory.Koecher.bound_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:50:13.523853+00:00
-- url     : https://prove2.me/submissions/fd4b528f-e26a-4e7b-9f75-fa7464fdbb80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Theorems.Thm_GlobalTheory_IsSiegel_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.Koecher
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
namespace GlobalTheory.Koecher
theorem _root_.solution {g : ℕ} {F : Matrix (Fin g) (Fin g) ℂ → ℂ}
    {U : Matrix (Fin g) (Fin g) ℤ} (hU : U.det = 1)
    (hinv : ∀ τ ∈ SiegelH (Fin g),
      F (U.map (Int.cast : ℤ → ℂ) * τ * (U.map (Int.cast : ℤ → ℂ))ᵀ) = F τ)
    {s M : ℝ} (hs : 0 < s)
    (hM : ∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm →
      τ.map Complex.im = s • (1 : Matrix (Fin g) (Fin g) ℝ) → ‖F τ‖ ≤ M)
    (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τ.IsSymm)
    (him : τ.map Complex.im =
      s • (U.map (Int.cast : ℤ → ℝ) * (U.map (Int.cast : ℤ → ℝ))ᵀ)) : ‖F τ‖ ≤ M := by
  set V := U.adjugate with hV
  have hUV : U * V = 1 := by rw [hV, mul_adjugate, hU, one_smul]
  have hVU : V * U = 1 := by rw [hV, adjugate_mul, hU, one_smul]
  have hC : U.map (Int.cast : ℤ → ℂ) * V.map (Int.cast : ℤ → ℂ) = 1 := by
    have := congrArg (Int.castRingHom ℂ).mapMatrix hUV
    rwa [map_mul, map_one] at this
  have hR : V.map (Int.cast : ℤ → ℝ) * U.map (Int.cast : ℤ → ℝ) = 1 := by
    have := congrArg (Int.castRingHom ℝ).mapMatrix hVU
    rwa [map_mul, map_one] at this
  set σ := V.map (Int.cast : ℤ → ℂ) * τ * (V.map (Int.cast : ℤ → ℂ))ᵀ with hσ
  have hσs : σ.IsSymm := by
    rw [Matrix.IsSymm, hσ, transpose_mul, transpose_mul, transpose_transpose, hτ.eq,
      Matrix.mul_assoc]
  have hσim : σ.map Complex.im = s • (1 : Matrix (Fin g) (Fin g) ℝ) := by
    have e : σ.map Complex.im =
        V.map (Int.cast : ℤ → ℝ) * τ.map Complex.im * (V.map (Int.cast : ℤ → ℝ))ᵀ := by
      ext i j
      simp [hσ, Matrix.mul_apply, Complex.im_sum]
    rw [e, him, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hR, Matrix.one_mul,
      ← transpose_mul, hR, transpose_one]
  have hτσ : U.map (Int.cast : ℤ → ℂ) * σ * (U.map (Int.cast : ℤ → ℂ))ᵀ = τ := by
    rw [hσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hC, Matrix.one_mul, Matrix.mul_assoc,
      ← transpose_mul, hC, transpose_one, Matrix.mul_one]
  rw [← hτσ, hinv σ ⟨hσs, by rw [hσim]; exact Matrix.PosDef.one.smul hs⟩]
  exact hM σ hσs hσim
end GlobalTheory.Koecher
