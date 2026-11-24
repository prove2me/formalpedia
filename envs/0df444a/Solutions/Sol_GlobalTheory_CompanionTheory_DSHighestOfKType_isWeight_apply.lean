-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSHighestOfKType.isWeight_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:11.972796+00:00
-- url     : https://prove2.me/submissions/d61fb8ec-7f69-493f-a1de-958725f45ff6

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NotCdomAddRoot
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSHighestOfKType
open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSHighestOfKType
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {μ : Fin n → ℝ} {v : V} (hv : IsWeight E μ v) (a b : Fin n) :
    IsWeight E (μ + root a b) (E a b v) := by
  intro c
  have h := LinearMap.congr_fun (hE c c a b) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [root]
  · subst h1; simp [root, h2, Ne.symm h2, add_smul, add_comm]
  · subst h2; simp [root, h1, add_smul, add_comm]
  · simp [root, h1, h2, Ne.symm h2]
end GlobalTheory.CompanionTheory.DSHighestOfKType
