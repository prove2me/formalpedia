-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.appTop_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:11:51.213247+00:00
-- url     : https://prove2.me/submissions/50178c89-9ac9-4ae2-afab-aa17487c3e16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {Y Z : Scheme.{0}} (D : Y.Opens) {B : CommRingCat.{0}} (φ : B ⟶ Γ(Y, D))
    (g : Z ⟶ D.toScheme) :
    (g ≫ D.toSpecΓ ≫ Spec.map φ).appTop =
      (Scheme.ΓSpecIso B).hom ≫ φ ≫ (g ≫ D.ι).appLE D ⊤ (le_pre D g) := by
  have e : D.topIso.inv ≫ g.appTop = (g ≫ D.ι).appLE D ⊤ (le_pre D g) := by
    rw [← Scheme.Hom.appLE_comp_appLE g D.ι D ⊤ ⊤ (by simp) le_top]
    congr 1
    · rw [Scheme.Opens.ι_appLE]; rfl
    · exact Scheme.Hom.app_eq_appLE g
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop, ← e]
  simp only [Category.assoc]
  rw [Scheme.ΓSpecIso_naturality_assoc]
end GlobalTheory.VeryAmplePow
