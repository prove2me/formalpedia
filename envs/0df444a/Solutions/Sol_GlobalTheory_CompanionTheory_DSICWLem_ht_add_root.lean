-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICWLem.ht_add_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:13.894828+00:00
-- url     : https://prove2.me/submissions/a929a422-9bea-4c6d-bdc9-080bfb213629

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WlemOfGfacts
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICWLem
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
namespace GlobalTheory.CompanionTheory.DSICWLem
theorem _root_.solution {n : ℕ} (w : Fin n → ℝ) (c d : Fin n) (h : c < d) :
    ht w < ht (w + Pi.single c 1 - Pi.single d 1) := by
  have hcd : ((c : ℕ) : ℝ) < ((d : ℕ) : ℝ) := by exact_mod_cast h
  have : ht (w + Pi.single c 1 - Pi.single d 1) =
      ht w + ((n : ℝ) - (c : ℕ)) - ((n : ℝ) - (d : ℕ)) := by
    simp [ht, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
  rw [this]
  linarith
end GlobalTheory.CompanionTheory.DSICWLem
