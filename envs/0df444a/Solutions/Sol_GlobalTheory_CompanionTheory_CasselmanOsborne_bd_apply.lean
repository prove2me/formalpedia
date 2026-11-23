-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.bd_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:27.827117+00:00
-- url     : https://prove2.me/submissions/2819bd4a-3c93-4d9e-92c9-d030bf93ace4

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (x : Ch ε V) (A : Finset (NC ε)) :
    bd ε E x A = ∑ i : NC ε, E i.1.1 i.1.2 (if i ∈ A then 0 else sg i A • x (insert i A)) := by
  simp [bd, bdA, LinearMap.sum_apply, Finset.sum_apply, ann]
end GlobalTheory.CompanionTheory.CasselmanOsborne
