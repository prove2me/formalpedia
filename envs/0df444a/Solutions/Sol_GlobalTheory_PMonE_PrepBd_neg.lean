-- Prove2me | solution 1 for GlobalTheory.PMonE.PrepBd.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:11.767803+00:00
-- url     : https://prove2.me/submissions/32402427-cf04-4aaa-a0ec-3eb2bd60c761

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
theorem _root_.solution {c : ℝ} {X : Matrix m m F} (hX : PrepBd c X) : PrepBd c (-X) :=
  fun i j => by simpa using hX i j
end PrepBd
end GlobalTheory.PMonE
