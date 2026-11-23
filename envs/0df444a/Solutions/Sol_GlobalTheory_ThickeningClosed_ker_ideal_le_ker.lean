-- Prove2me | solution 1 for GlobalTheory.ThickeningClosed.ker_ideal_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:34.183225+00:00
-- url     : https://prove2.me/submissions/be66be1f-c869-42a0-b399-374bbf81bd03

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ThickeningClosed
namespace _root_.GlobalTheory.ThickeningClosed
theorem _root_.solution {X Z : Scheme.{0}} (ι : Z ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) {D : CommRingCat.{0}} (ψ : Γ(X, U) ⟶ D) (l : Spec D ⟶ Z)
    (hl : l ≫ ι = Spec.map ψ ≫ hU.fromSpec) :
    ι.ker.ideal ⟨U, hU⟩ ≤ RingHom.ker ψ.hom := by
  intro a ha
  have h0 : ι.app U a = 0 := ι.ideal_ker_le ⟨U, hU⟩ ha
  have e : (⊤ : (Spec D).Opens) ≤ (l ≫ ι) ⁻¹ᵁ U := by
    rw [hl, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]; simp
  have h1 : (l ≫ ι).appLE U ⊤ e a = 0 := by
    rw [Scheme.Hom.comp_appLE]; simp [h0]
  have h2 : ∀ (g) (_ : g = Spec.map ψ ≫ hU.fromSpec) (e : (⊤ : (Spec D).Opens) ≤ g ⁻¹ᵁ U),
      g.appLE U ⊤ e = ψ ≫ (Scheme.ΓSpecIso D).inv := by
    rintro g rfl e
    rw [Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_self, Category.assoc]
    erw [Scheme.Hom.map_appLE]
    rw [Iso.inv_comp_eq, ← cancel_mono (Scheme.ΓSpecIso D).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Scheme.ΓSpecIso_naturality]
    rfl
  rw [h2 _ hl e, CommRingCat.comp_apply] at h1
  rw [RingHom.mem_ker]
  have h3 := congrArg (Scheme.ΓSpecIso D).hom.hom h1
  rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h3
end _root_.GlobalTheory.ThickeningClosed
end GlobalTheory.ThickeningClosed
