-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainCAR.key_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:22:55.980138+00:00
-- url     : https://prove2.me/submissions/0d15d2d4-9c37-453f-ae7e-ffa5abb71198

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
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
namespace GlobalTheory.CompanionTheory.ChainCAR
theorem _root_.solution {i j : NC ε} (h : key i = key j) : i = j := by
  unfold key at h
  have hi := i.1.2.2
  have hj := j.1.2.2
  have hn : 0 < n := by omega
  have h2 : (i.1.2 : ℕ) = j.1.2 := by
    have := congrArg (· % n) h
    simpa [Nat.mul_add_mod_of_lt hi, Nat.mul_add_mod_of_lt hj] using this
  have h1 : (i.1.1 : ℕ) = j.1.1 := by
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right hn (Nat.add_right_cancel h)
  exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))
end GlobalTheory.CompanionTheory.ChainCAR
