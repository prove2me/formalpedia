-- Prove2me | solution 2 for OAI.Cotype.projectionGenerator_exp_shift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:01:32.413189+00:00
-- url     : https://prove2.me/submissions/86f47b18-a091-4ad6-a517-4aed4bf3ad28

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionResolvent.lean:L10-L39
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.projectionGenerator_exp_shift. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Theorems.Thm_OAI_Cotype_complexProjectionTime_eq_exp

-- ---- from OAI.Analysis.Cotype.ProjectionResolvent ----
namespace OAI

noncomputable section
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem projectionGenerator_exp_shift {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (z : ℂ) (s : ℝ) :
    NormedSpace.exp (s • (z • 1 - projectionGenerator P)) =
      Complex.exp (z * (s : ℂ)) • complexProjectionTime P (s : ℂ) := by
  let : NormedAlgebra ℚ (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  rw [complexProjectionTime_eq_exp P hp hc]
  have hsplit : s • (z • 1 - projectionGenerator P) =
      (z * (s : ℂ)) • 1 + (-(s : ℂ)) • projectionGenerator P := by
    ext vector dual
    simp [Complex.real_smul, smul_eq_mul]
    ring
  have hcommute : Commute ((z * (s : ℂ)) •
      (1 : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y))
      ((-(s : ℂ)) • projectionGenerator P) := by
    apply ContinuousLinearMap.ext
    intro vector
    change (z * (s : ℂ)) • ((-(s : ℂ)) • projectionGenerator P vector) =
      (-(s : ℂ)) • projectionGenerator P ((z * (s : ℂ)) • vector)
    rw [(projectionGenerator P).map_smul]
    ext dual
    exact mul_left_comm _ _ _
  rw [hsplit, NormedSpace.exp_add_of_commute hcommute]
  have he := NormedSpace.algebraMap_exp_comm
    (𝕂 := ℂ) (𝔸 := ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) (z * (s : ℂ))
  simp only [Algebra.algebraMap_eq_smul_one, ← Complex.exp_eq_exp_ℂ] at he
  rw [← he]
  ext vector dual
  rfl

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.projectionGenerator_exp_shift := @_root_.OAI.Cotype.projectionGenerator_exp_shift
