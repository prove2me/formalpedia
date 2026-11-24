-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.deg_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:22:33.923732+00:00
-- url     : https://prove2.me/submissions/a2ef86f0-b1a2-473b-a724-e6f61485890d

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_bd_apply
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
theorem _root_.solution {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) {x : Ch ε V} (hx : Deg (j + 1) x) :
    Deg j (bd ε E x) := by
  intro A hA
  rw [bd_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h
  · simp
  · rw [hx _ (by rw [Finset.card_insert_of_notMem h]; omega)]
    simp
end GlobalTheory.CompanionTheory.CasselmanOsborne
