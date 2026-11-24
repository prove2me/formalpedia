-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.euler_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:49:53.229381+00:00
-- url     : https://prove2.me/submissions/de0166b8-3058-427d-af32-706dcd1357e7

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_euler_ring
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_mem_filt_succ
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] {ι : Type*}
namespace GlobalTheory.CompanionTheory.DSICKoszul
theorem _root_.solution [Fintype ι] [DecidableEq ι] (a d : ι → Module.End ℂ Z) (h2 : ∀ i j, Commute (d i) (d j))
    (h3 : ∀ i j, d i * a j - a j * d i = if i = j then 1 else 0) (m : ℕ) (z : Z)
    (hz : z ∈ filt d (m + 1)) : (∑ j, a j * d j) z - (m : ℂ) • z ∈ filt d m := by
  induction m generalizing z with
  | zero =>
    rw [mem_filt_succ] at hz
    have h0 : ∀ i, d i z = 0 := fun i => by simpa [filt] using hz i
    simp [filt, LinearMap.sum_apply, h0]
  | succ m ih =>
    rw [mem_filt_succ] at hz ⊢
    intro i
    have e := congrArg (fun T : Module.End ℂ Z => T z) (euler_ring a d h2 h3 i)
    simp only [Module.End.mul_apply, LinearMap.add_apply] at e
    have := ih _ (hz i)
    convert this using 1
    rw [map_sub, e, map_smul]
    push_cast
    rw [add_smul, one_smul]
    abel
end GlobalTheory.CompanionTheory.DSICKoszul
