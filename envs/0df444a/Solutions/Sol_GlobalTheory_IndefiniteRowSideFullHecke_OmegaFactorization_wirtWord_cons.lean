-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:59.581808+00:00
-- url     : https://prove2.me/submissions/cf300cb4-3527-4c96-9702-693caf46d858

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable (F : Type) [Field F] [NumberField F]
variable {F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
theorem _root_.solution {Φ : Type} [Fintype Φ] (w : Φ × Bool) (ws : List (Φ × Bool)) (g : (Φ → ℂ) → ℂ) :
    wirtWord (w :: ws) g = wirt w.1 w.2 (wirtWord ws g) := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
