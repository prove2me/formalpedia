-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCover.glRel_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:29.931865+00:00
-- url     : https://prove2.me/submissions/add4c817-fe41-4467-9ac5-5cd59ab5ae8c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
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
open scoped TensorProduct
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCover
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC
namespace GlobalTheory.CompanionTheory.DSCover
theorem _root_.solution {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) :
    GlRel fun a b => φ (E a b) := by
  intro a b c d
  have h := congrArg φ (hE a b c d)
  simp only [map_sub, map_mul] at h
  rw [h]
  split_ifs <;> simp
end GlobalTheory.CompanionTheory.DSCover
