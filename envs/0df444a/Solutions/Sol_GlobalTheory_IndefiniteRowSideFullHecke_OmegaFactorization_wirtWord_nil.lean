-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:35.104318+00:00
-- url     : https://prove2.me/submissions/d5ec3873-a596-4eb4-85ba-7ecab637e0ad

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
theorem _root_.solution {Φ : Type} [Fintype Φ] (g : (Φ → ℂ) → ℂ) : wirtWord [] g = g := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
