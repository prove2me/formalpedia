-- Prove2me | solution 1 for GlobalTheory.PMonE.PrepBd.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:06.088714+00:00
-- url     : https://prove2.me/submissions/6fecda71-5cde-4251-a9f9-c62a6a06a856

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
omit [Fintype m]
namespace GlobalTheory.PMonE
namespace PrepBd
theorem _root_.solution {c : ℝ} {X Y : Matrix m m F} (hX : PrepBd c X) (hY : PrepBd c Y) : PrepBd c (X + Y) :=
  fun i j => (IsUltrametricDist.norm_add_le_max (X i j) (Y i j)).trans (max_le (hX i j) (hY i j))
end PrepBd
end GlobalTheory.PMonE
