-- Prove2me | solution 1 for GlobalTheory.PMonE.PrepBd.map_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:28.117819+00:00
-- url     : https://prove2.me/submissions/08c4a31d-71d7-4ebd-803a-d29cf97ee4f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] {m : Type} [Fintype m]
variable [IsUltrametricDist F]
omit [Fintype m] [IsUltrametricDist F]
namespace GlobalTheory.PMonE
namespace PrepBd
theorem _root_.solution {X : Matrix m m F} (hX : PrepBd 1 X) (N : ℕ) : PrepBd 1 (X.map (fun a => a ^ N)) := by
  intro i j
  rw [Matrix.map_apply, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hX i j)
end PrepBd
end GlobalTheory.PMonE
