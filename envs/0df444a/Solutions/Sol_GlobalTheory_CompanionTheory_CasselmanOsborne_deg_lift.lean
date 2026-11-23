-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.deg_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:25.038236+00:00
-- url     : https://prove2.me/submissions/48e7dbdf-7a58-4fd7-a893-273734a88bdc

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
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution {j : ℕ} (φ : V →ₗ[ℂ] W) {x : Ch ε V} (hx : Deg j x) : Deg j (lift ε φ x) :=
  fun A hA => by simp [hx A hA]
end GlobalTheory.CompanionTheory.CasselmanOsborne
