-- Prove2me | solution 1 for HlawkaSchatten.schattenPNorm_two_hasHlawkaConstant
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T00:03:29.756862+00:00
-- url     : https://prove2.me/submissions/c9e2ce89-2015-43f7-a411-6da719243fd7

import Definitions.Def_HlawkaSchatten_HilbertSchmidt
import Definitions.Def_HlawkaSchatten_GapComparison
import Theorems.Thm_HlawkaSchatten_norm_pair_sums_le

open HlawkaSchatten

/-- The Schatten-2 quantity is the Hilbert norm of the column coordinates. -/
theorem schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates
    {𝕜 E F ι : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (e : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] F) :
    schattenPNorm 2 T = ‖hilbertSchmidtCoordinates e T‖ := by
  unfold schattenPNorm
  rw [singularValuePowerSum_two_eq_norm_hilbertSchmidtCoordinates_sq e T,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

/-- Every inner-product norm has Hlawka constant one. -/
theorem norm_hasHlawkaConstant
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    HasHlawkaConstant (norm : E → ℝ) 1 := by
  intro x y z
  dsimp only [tripleGap, pairGapSum, pairGap]
  have h := norm_pair_sums_le (𝕜 := 𝕜) x y z
  simp only [one_mul]
  linarith

/-- The finite-dimensional Schatten-2 quantity has Hlawka constant one. -/
theorem solution
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] :
    HasHlawkaConstant (schattenPNorm 2 : (E →ₗ[𝕜] F) → ℝ) 1 := by
  let e := stdOrthonormalBasis 𝕜 E
  intro x y z
  have h := norm_hasHlawkaConstant (𝕜 := 𝕜)
    (hilbertSchmidtCoordinates e x)
    (hilbertSchmidtCoordinates e y)
    (hilbertSchmidtCoordinates e z)
  dsimp only [tripleGap, pairGapSum, pairGap] at h ⊢
  simp only [← hilbertSchmidtCoordinates_add] at h
  simpa only [schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates e] using h
