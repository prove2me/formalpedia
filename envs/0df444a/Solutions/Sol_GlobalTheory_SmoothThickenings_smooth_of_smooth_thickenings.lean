-- Prove2me | solution 1 for GlobalTheory.SmoothThickenings.smooth_of_smooth_thickenings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:57:52.394119+00:00
-- url     : https://prove2.me/submissions/e78291cf-9278-4df9-9392-c064fad39df8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSmoothAtOfSmoothModIdealPowersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothOfSmoothThickenings
import Theorems.Thm_GlobalTheory_SmoothThickenings_mem_smoothLocus
import Theorems.Thm_GlobalTheory_SmoothLimit_mem_smoothLocus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SmoothThickenings
namespace GlobalTheory.SmoothThickenings
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (B : Over (Spec (CommRingCat.of R))), IsProper B.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, Smooth (Y e).hom) → Smooth B.hom := by
  intro R _ _ _ I hI B _ Y b hpb hY
  have : LocallyOfFinitePresentation B.hom := inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z, z ∉ B.hom.smoothLocus := by
    by_contra! H
    exact hne (eq_top_iff.mpr fun z _ => H z)
  have hcl : IsClosed (B.hom '' (B.hom.smoothLocus : Set B.left)ᶜ) :=
    B.hom.isClosedMap _ B.hom.smoothLocus.2.isClosed_compl
  obtain ⟨z', hz', hz'c⟩ :=
    (IsLocalRing.specializes_closedPoint (B.hom z)).mem_closed hcl ⟨z, hz, rfl⟩
  apply hz'
  refine mem_smoothLocus I hI B.hom (fun e => ?_) z' hz'c
  rw [← (hpb e).isoPullback_inv_snd]
  have := hY e
  infer_instance
end GlobalTheory.SmoothThickenings
