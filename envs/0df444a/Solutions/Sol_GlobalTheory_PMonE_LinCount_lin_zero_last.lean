-- Prove2me | solution 1 for GlobalTheory.PMonE.LinCount.lin_zero_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:24.670732+00:00
-- url     : https://prove2.me/submissions/4159a964-3382-46ed-9981-a2d66a2d6ba4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LinCount
open Finset GlobalTheory.PMonE
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
namespace GlobalTheory.PMonE.LinCount
theorem _root_.solution (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M 0).mulVec Y (Fin.last K, a) = ∑ j : Fin (K + 1), (M j).mulVec (fun b => Y (j, b)) a := by
  simp [Matrix.mulVec, dotProduct, lin, Fintype.sum_prod_type]
end GlobalTheory.PMonE.LinCount
