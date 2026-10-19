-- Prove2me | solution 1 for HlawkaSchatten.SchattenSharpness.cyclic_bound256
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-16T22:02:56.622077+00:00
-- url     : https://prove2.me/submissions/ba86ecb6-ee29-4762-a522-d46a8a4653a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HlawkaSchatten_SchattenNorm
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_HermitianDilation
import Theorems.Thm_HlawkaSchatten_SchattenSharpness_selfAdjoint_cyclic_bound256

/-!
# The general cyclic bound reduces to self-adjoint operators

The off-diagonal Hermitian dilation `T ↦ [[0, T†], [T, 0]]` is additive, its
values are self-adjoint, and it multiplies every Schatten `p`-norm by `2 ^ (1 / p)`.
Every gap in the Hlawka inequality therefore scales by the same positive factor,
so the self-adjoint bound for the dilated triple gives the bound for the
original rectangular triple.
-/

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

namespace HlawkaSchatten.SchattenSharpness.DilationReduction

/-- The functional calculus depends only on the operator, not on the proof of
its symmetry. -/
theorem hermitianFunctionalCalculus_congr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (f : ℝ → ℝ) {A B : H →ₗ[ℂ] H} (h : A = B)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    hermitianFunctionalCalculus f A hA = hermitianFunctionalCalculus f B hB := by
  subst h
  rfl

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The Hermitian dilation doubles the singular-value power sum. -/
theorem singularValuePowerSum_hermitianDilation
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    singularValuePowerSum p (hermitianDilation T) =
      2 * singularValuePowerSum p T := by
  have hD : (hermitianDilation T).IsSymmetric := hermitianDilation_isSymmetric T
  have hgram := re_trace_gramPowerPotential_eq_singularValuePowerSum_div hp
    (hermitianDilation T)
  rw [hermitianFunctionalCalculus_congr (fun y ↦ y ^ (p / 2) / p)
      (by rw [hD.adjoint_eq]) _ (isSymmetric_comp_self _ hD),
    ← hermitianFunctionalCalculus_powerPotential_comp_self p _ hD,
    re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum hp T] at hgram
  field_simp at hgram
  linarith

/-- The Hermitian dilation multiplies the Schatten `p`-norm by `2 ^ (1 / p)`. -/
theorem schattenPNorm_hermitianDilation
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    schattenPNorm p (hermitianDilation T) = 2 ^ (1 / p) * schattenPNorm p T := by
  unfold schattenPNorm
  rw [singularValuePowerSum_hermitianDilation hp T,
    Real.mul_rpow (by norm_num) (singularValuePowerSum_nonneg p T)]

end HlawkaSchatten.SchattenSharpness.DilationReduction

open HlawkaSchatten.SchattenSharpness.DilationReduction

theorem solution
    (p : ℝ) (hp : 256 ≤ p)
    (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] :
    HasHlawkaConstant (schattenPNorm p : (E →ₗ[ℂ] F) → ℝ)
      (cyclicConstant p) := by
  have hp0 : 0 < p := by linarith
  have hc : (0 : ℝ) < 2 ^ (1 / p) := by positivity
  have hN : ∀ T : E →ₗ[ℂ] F,
      schattenPNorm p (hermitianDilation T) = 2 ^ (1 / p) * schattenPNorm p T :=
    fun T ↦ schattenPNorm_hermitianDilation hp0 T
  intro x y z
  have key := HlawkaSchatten.SchattenSharpness.selfAdjoint_cyclic_bound256 p hp
    (WithLp 2 (E × F)) (hermitianDilation x) (hermitianDilation y) (hermitianDilation z)
    (hermitianDilation_isSymmetric x) (hermitianDilation_isSymmetric y)
    (hermitianDilation_isSymmetric z)
  simp only [tripleGap, pairGapSum, pairGap, ← hermitianDilation_add, hN] at key
  simp only [tripleGap, pairGapSum, pairGap]
  refine le_of_mul_le_mul_left ?_ hc
  linarith [key]
