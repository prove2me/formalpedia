-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.gop_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:17.865461+00:00
-- url     : https://prove2.me/submissions/0579c77d-80ff-4e01-9552-d2ba38efca36

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
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
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSICFRel
theorem _root_.solution (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (c d : Fin n) :
    (Gop ε c d : Module.End ℂ (Ch ε V)) = bil cre ann (fun i j : NC ε => mm c d i.1 j.1) := by
  unfold Gop bil
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [mm, dl, ite_and, mul_ite, mul_one, mul_zero]
  split_ifs <;> simp_all
end GlobalTheory.CompanionTheory.DSICFRel
