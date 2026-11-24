-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.IsCompletedL.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:36:39.953732+00:00
-- url     : https://prove2.me/submissions/ca76090f-4d80-482b-ba5f-eb14aa375e67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Theorems.Thm_GlobalTheory_CMVal_ExpAt_unique
import Theorems.Thm_GlobalTheory_CMVal_IsHeckeL_unique
import Theorems.Thm_GlobalTheory_CMVal_IsLatSum_unique
import Theorems.Thm_GlobalTheory_CMVal_IsToricSum_unique
import Theorems.Thm_GlobalTheory_CMVal_entire_eq_of_halfPlane


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
namespace IsCompletedL
theorem _root_.solution {χ : HChar E} {n : I → ℤ} {f g : ℂ → ℂ} (hf : IsCompletedL χ n f) (hg : IsCompletedL χ n g) :
    f = g :=
  entire_eq_of_halfPlane hf.1 hg.1 1 fun s hs => by
    obtain ⟨L, h1, h2⟩ := hf.2 s hs
    obtain ⟨L', h1', h2'⟩ := hg.2 s hs
    rw [h2, h2', h1.unique h1']
end IsCompletedL
end GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
