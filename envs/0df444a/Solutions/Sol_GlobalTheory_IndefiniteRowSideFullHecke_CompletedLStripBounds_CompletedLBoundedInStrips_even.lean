-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips.even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:30.7548+00:00
-- url     : https://prove2.me/submissions/5c1be73f-86b6-409a-ae0e-0cd7eaf390e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompletedLStripBounds_archFactor_two_mul
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
namespace CompletedLBoundedInStrips
theorem _root_.solution (h : CompletedLBoundedInStrips) : CompletedLBoundedInStripsEven := by
  intro E _ _ _ I _ φ hφ χ m hu hi ⟨i, hm⟩
  obtain ⟨Λ, h1, h2⟩ := h E I φ hφ χ (fun i => 2 * m i) hu hi ⟨i, mul_ne_zero two_ne_zero hm⟩
  refine ⟨Λ, h1.1, fun s hs => ?_, h2⟩
  simpa only [archFactor_two_mul] using h1.2 s hs
end CompletedLBoundedInStrips
end GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
