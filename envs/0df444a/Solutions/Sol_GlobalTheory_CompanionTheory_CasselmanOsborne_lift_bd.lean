-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.lift_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:25.045926+00:00
-- url     : https://prove2.me/submissions/a5ac899d-e3ef-4f02-91c8-b99fcccbfa3a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_bd_apply
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
theorem _root_.solution (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (x : Ch ε V) : lift ε φ (bd ε E x) = bd ε F (lift ε φ x) := by
  funext A
  rw [lift_apply, bd_apply, bd_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h]
  split_ifs <;> simp
end GlobalTheory.CompanionTheory.CasselmanOsborne
