-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.ind_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:16.276836+00:00
-- url     : https://prove2.me/submissions/225c9bc0-4279-4c81-96cd-8b34b5de8ed6

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSNormLt
theorem _root_.solution {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ε a = true ∧ ε b = false) :
    ind A a b = if (⟨(a, b), h⟩ : NC ε) ∈ A then 1 else 0 := by
  unfold ind
  congr 1
  simp [h]
end GlobalTheory.CompanionTheory.DSNormLt
