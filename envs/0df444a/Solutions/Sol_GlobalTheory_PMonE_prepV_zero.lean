-- Prove2me | solution 1 for GlobalTheory.PMonE.prepV_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:28.38067+00:00
-- url     : https://prove2.me/submissions/d2734dcc-c67d-4623-908a-6f630f9b08ed

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
theorem _root_.solution (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (n : ℕ) : prepV q M A 0 n = 0 := rfl
end GlobalTheory.PMonE
