-- Prove2me | solution 1 for GlobalTheory.PMonE.prepV_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:08.88536+00:00
-- url     : https://prove2.me/submissions/732da8c3-36c9-45f6-8128-64185e4225c3

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
namespace GlobalTheory.PMonE
theorem _root_.solution (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (k n : ℕ) :
    prepV q M A (k + 1) n = M (n + 1) + prepV q M A k (n + 1) * A.map (fun a => a ^ q ^ (n + 1)) := rfl
end GlobalTheory.PMonE
