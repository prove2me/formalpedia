-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KoszulBd.lift_cre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:40.605158+00:00
-- url     : https://prove2.me/submissions/0fadf712-2390-4907-90ea-83a62cd5f4e0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfUnitaryConjugate
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KoszulBd
open CompanionTheory.D.DSIC
open Formalism.REAL (GlRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.KoszulBd
theorem _root_.solution (T : Module.End ℂ V) (i : NC ε) :
    Commute (lift ε T : Module.End ℂ (Ch ε V)) (cre i) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  show T (cre i x A) = cre i (lift ε T x) A
  simp only [cre, LinearMap.coe_mk, AddHom.coe_mk, lift_apply]
  split_ifs
  · exact map_smul T _ _
  · exact map_zero T
end GlobalTheory.CompanionTheory.KoszulBd
