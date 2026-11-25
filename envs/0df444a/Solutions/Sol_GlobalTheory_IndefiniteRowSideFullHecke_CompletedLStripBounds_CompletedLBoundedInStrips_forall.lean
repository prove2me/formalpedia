-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips.forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:34.770823+00:00
-- url     : https://prove2.me/submissions/dc5faac5-6343-48b5-8d12-678943a26cf7

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
namespace CompletedLBoundedInStrips
theorem _root_.solution (h : CompletedLBoundedInStrips) [IsTotallyComplex E] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {χ : HChar E} {n : I → ℤ} (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0)
    {Λ : ℂ → ℂ} (hΛ : IsCompletedL χ n Λ) : BoundedInStrips Λ := by
  obtain ⟨Λ', h1, h2⟩ := h E I φ hφ χ n hu hi hn
  rwa [hΛ.unique h1]
end CompletedLBoundedInStrips
end GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
