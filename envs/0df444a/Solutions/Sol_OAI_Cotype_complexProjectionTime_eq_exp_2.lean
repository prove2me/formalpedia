-- Prove2me | solution 2 for OAI.Cotype.complexProjectionTime_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:55:39.552578+00:00
-- url     : https://prove2.me/submissions/b29d3da1-fecf-4c4e-8092-b8b15dc3042f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionGenerator.lean:L43-L57
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.complexProjectionTime_eq_exp. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_complexProjectionPolynomial_spectral

-- ---- from OAI.Analysis.Cotype.ProjectionGenerator ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem complexProjectionTime_eq_exp {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j)) (t : ℂ) :
    complexProjectionTime P t = NormedSpace.exp ((-t) • projectionGenerator P) := by
  let H := complexProjectionSpectralHom P hp hc
  have hH : Continuous H := H.toLinearMap.continuous_of_finiteDimensional
  change complexProjectionTime P t = NormedSpace.exp ((-t) • H (fun ε => (projectionDegree ε : ℂ)))
  rw [← map_smul, ← NormedSpace.map_exp H hH]
  rw [complexProjectionTime, complexProjectionPolynomial_spectral]
  change complexSpectralEval P _ = complexSpectralEval P _
  congr 1
  funext ε
  simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.complexProjectionTime_eq_exp := @_root_.OAI.Cotype.complexProjectionTime_eq_exp
