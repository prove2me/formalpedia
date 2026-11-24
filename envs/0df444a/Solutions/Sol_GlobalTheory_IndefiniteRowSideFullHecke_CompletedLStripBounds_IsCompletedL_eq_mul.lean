-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.IsCompletedL.eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:38:36.636537+00:00
-- url     : https://prove2.me/submissions/32ed8986-6263-4026-8dce-ac72953dd2e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompletedLStripBounds_IsCompletedL_unique
import Theorems.Thm_GlobalTheory_CMVal_ExpAt_unique
import Theorems.Thm_GlobalTheory_CMVal_IsHeckeL_unique
import Theorems.Thm_GlobalTheory_CMVal_IsLatSum_unique
import Theorems.Thm_GlobalTheory_CMVal_IsToricSum_unique


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
theorem _root_.solution {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ) (hL : IsHeckeL χ L)
    {s : ℂ} (hs : 1 < s.re) : Λ s = archFactor n s * L s := by
  obtain ⟨L', h1, h2⟩ := h.2 s hs
  rw [h2, h1.unique (hL.2 s hs)]
end IsCompletedL
end GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
