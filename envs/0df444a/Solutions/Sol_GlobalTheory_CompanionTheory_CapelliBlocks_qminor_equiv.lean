-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliBlocks.qminor_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:54.299902+00:00
-- url     : https://prove2.me/submissions/470e1fe6-b69f-4099-9249-45a92ceffd83

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_Formalism_REAL_qSkewCol
import Theorems.Thm_Formalism_REAL_qSkewRow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset Equiv
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliBlocks
open Formalism.REAL CompanionTheory.D.DSIC
namespace GlobalTheory.CompanionTheory.CapelliBlocks
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {m n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (τ : Fin m ≃ Fin n) (u : ℂ) : qminor E τ τ u = qdet E u := by
  obtain rfl : m = n := Fin.equiv_iff_eq.mp ⟨τ⟩
  have hr := qSkewRow A m m E id (τ : Fin m → Fin m) τ u
  have hc := qSkewCol A m m E hE id id τ u
  simp only [Function.id_comp] at hr hc
  rw [hr, hc, ← mul_assoc, ← Int.cast_mul, qdet]
  have : ((Perm.sign τ : ℤˣ) : ℤ) * (Perm.sign τ : ℤˣ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  rw [this, Int.cast_one, one_mul]
end GlobalTheory.CompanionTheory.CapelliBlocks
