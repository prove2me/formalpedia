-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KModExists.glRel_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:40:50.887025+00:00
-- url     : https://prove2.me/submissions/c4c40bf7-077c-4ff7-8b28-6be53b5ea701

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactFiniteAdelesAwayPBoundedDenominators
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
open Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KModExists
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (IsKFin IsKTypeOf IsKStableOn)
open CompanionTheory.D.DSIC
namespace GlobalTheory.CompanionTheory.KModExists
theorem _root_.solution {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : V →ₗ[ℂ] W) (hι : Function.Injective ι) (E' : Fin n → Fin n → Module.End ℂ V)
    (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b v, ι (E' a b v) = E a b (ι v)) (hE : GlRel E) :
    GlRel E' := by
  intro a b c d
  ext v
  apply hι
  have := LinearMap.congr_fun (hE a b c d) (ι v)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, h]
  rw [this]
  split_ifs <;> simp [h]
end GlobalTheory.CompanionTheory.KModExists
