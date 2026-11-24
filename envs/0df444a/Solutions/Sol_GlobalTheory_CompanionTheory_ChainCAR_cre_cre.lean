-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainCAR.cre_cre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:56:29.772972+00:00
-- url     : https://prove2.me/submissions/8d043c9e-25ff-4a46-b943-3e202489a25b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_tw_swap
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_sg_erase
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_cre_apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainCAR
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.ChainCAR
theorem _root_.solution (i j : NC ε) : (cre i * cre j + cre j * cre i : Module.End ℂ (Ch ε V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    cre_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sg_erase j hi, sg_erase i hj, tw_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]
end GlobalTheory.CompanionTheory.ChainCAR
