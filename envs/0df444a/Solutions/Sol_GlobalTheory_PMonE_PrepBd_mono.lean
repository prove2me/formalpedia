-- Prove2me | solution 1 for GlobalTheory.PMonE.PrepBd.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:17:30.367664+00:00
-- url     : https://prove2.me/submissions/354eccdc-bc91-4363-a06c-fd4e3a8f9757

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
theorem _root_.solution {c d : ℝ} {X : Matrix m m F} (hX : PrepBd c X) (h : c ≤ d) : PrepBd d X :=
  fun i j => (hX i j).trans h
end PrepBd
end GlobalTheory.PMonE
