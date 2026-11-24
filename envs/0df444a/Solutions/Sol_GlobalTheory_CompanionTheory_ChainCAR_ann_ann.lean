-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainCAR.ann_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:56:28.1488+00:00
-- url     : https://prove2.me/submissions/f58254fe-657e-4d87-b757-69f7af2f88aa

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_tw_swap
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_sg_insert
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_ann_apply
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
theorem _root_.solution (i j : NC ε) : (ann i * ann j + ann j * ann i : Module.End ℂ (Ch ε V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    ann_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert j hi, sg_insert i hj, tw_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]
end GlobalTheory.CompanionTheory.ChainCAR
