-- Prove2me | solution 1 for GlobalTheory.KS.PtDual.ev_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:36.038485+00:00
-- url     : https://prove2.me/submissions/eac42cff-1bed-4784-912f-ff8253b4100b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.PtDual
variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]
namespace GlobalTheory.KS.PtDual
theorem _root_.solution (φ : R →+* S) (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ W)
    (f : Γ(X, W)) : ev (spMap φ ≫ v) W h' f = φ (ev v W h f) := by
  have h1 : v.appLE W ⊤ h ≫ (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ ≫ v).appLE W ⊤ h' :=
    Scheme.Hom.appLE_comp_appLE ..
  have h2 : (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg _ ((Sp S).presheaf.map_id _)).trans (Category.comp_id _)
  have h3 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  unfold ev
  rw [← h1, h2, Category.assoc]
  erw [h3]
  rfl
end GlobalTheory.KS.PtDual
