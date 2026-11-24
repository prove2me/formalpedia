-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.Gop_deg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:22:59.773913+00:00
-- url     : https://prove2.me/submissions/cba7f919-33c1-4095-b396-0494969668c0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution (c d : Fin n) {x : Ch ε V} (hx : Deg 0 x) : Gop ε c d x = 0 := by
  have : ∀ j : NC ε, ann j x = 0 := by
    intro j
    funext A
    by_cases h : j ∈ A
    · simp [ann, h]
    · simp [ann, h, hx (insert j A) (by rw [Finset.card_insert_of_notMem h]; omega)]
  simp [Gop, LinearMap.sum_apply, this]
end GlobalTheory.CompanionTheory.CasselmanOsborne
