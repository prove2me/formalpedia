-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsBalancedSpace.eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:14:46.573487+00:00
-- url     : https://prove2.me/submissions/029f020a-9697-4e3b-9ba9-441ed5a39012

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_BalancedHermitianSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
open NumberField NumberField.IsCMField TensorProduct
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
namespace IsBalancedSpace
theorem _root_.solution {S : Submodule ℝ (Bil Y)} (h : IsBalancedSpace E S) : S = balancedSpace E Y :=
  Submodule.ext h
end IsBalancedSpace
end GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
