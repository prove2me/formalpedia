-- Prove2me | solution 2 for OAI.Cotype.cubeNoise_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:42:01.213076+00:00
-- url     : https://prove2.me/submissions/39ab8c88-4485-4f55-a818-27a160dcafb0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CubeNoise.lean:L69-L85
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.cubeNoise_norm_le. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.CubeNoise ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem cubeNoise_norm_le {n : ℕ} (f : Cube n → X) (u : Cube n) :
    ‖cubeNoise f u‖ ≤ cubeNoise (fun v => ‖f v‖) u := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [cubeNoise]
    split
    · exact (norm_add_le _ _).trans (by
        simp only [norm_smul, Real.norm_eq_abs, smul_eq_mul]
        norm_num
        linarith [ih (fun v => f (Fin.cons false v)) (Fin.tail u),
          ih (fun v => f (Fin.cons true v)) (Fin.tail u)])
    · exact (norm_add_le _ _).trans (by
        simp only [norm_smul, Real.norm_eq_abs, smul_eq_mul]
        norm_num
        linarith [ih (fun v => f (Fin.cons false v)) (Fin.tail u),
          ih (fun v => f (Fin.cons true v)) (Fin.tail u)])

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.cubeNoise_norm_le := @_root_.OAI.Cotype.cubeNoise_norm_le
