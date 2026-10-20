-- Prove2me | solution 2 for OAI.Cotype.average_norm_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:36:18.332517+00:00
-- url     : https://prove2.me/submissions/b7d0126e-4e94-483e-b2ba-9ac33c0f3e57

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshDuality.lean:L13-L28
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.average_norm_mul_le. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.WalshDuality ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem average_norm_mul_le {n : ℕ} (f : Cube n → X) (g : Cube n → Y) :
    average (fun u => ‖f u‖ * ‖g u‖) ≤ cubeL2 X f * cubeL2 Y g := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun u => ‖f u‖) (fun u => ‖g u‖)
  have hq : 0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ := by positivity
  calc
    _ ≤ (Fintype.card (Cube n) : ℝ)⁻¹ *
        (Real.sqrt (∑ u, ‖f u‖^2) * Real.sqrt (∑ u, ‖g u‖^2)) :=
      mul_le_mul_of_nonneg_left h hq
    _ = _ := by
      simp only [cubeL2, average, smul_eq_mul, Real.sqrt_mul hq]
      calc
        _ = (Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹))^2 *
            (Real.sqrt (∑ u, ‖f u‖^2) * Real.sqrt (∑ u, ‖g u‖^2)) := by
          rw [Real.sq_sqrt hq]
        _ = _ := by ring

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.average_norm_mul_le := @_root_.OAI.Cotype.average_norm_mul_le
