-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.pres_graph
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:28.408364+00:00
-- url     : https://prove2.me/submissions/7e0a9ef0-6bcb-4bb3-9a34-f6dba31de52c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution (φ : V →ₗ[ℂ] W) (S : Module.End ℂ V) (T : Module.End ℂ W) :
    Pres φ.graph S T ↔ ∀ x, φ (S x) = T (φ x) := by
  constructor
  · intro h x
    have := h x (φ x) (by simp)
    simpa using this.symm
  · intro h x y hxy
    have : y = φ x := by simpa using hxy
    simp [this, h]
end GlobalTheory.CompanionTheory.CasselmanOsborne
