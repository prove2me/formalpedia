-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.ind_of_not
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:31.351807+00:00
-- url     : https://prove2.me/submissions/ded81e43-e137-4137-94b2-876043e3f382

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSNormLt
theorem _root_.solution {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ¬ (ε a = true ∧ ε b = false)) :
    ind A a b = 0 := by
  unfold ind
  rw [if_neg]
  rintro ⟨h', _⟩
  exact h h'
end GlobalTheory.CompanionTheory.DSNormLt
