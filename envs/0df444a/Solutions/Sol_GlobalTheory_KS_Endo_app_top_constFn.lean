-- Prove2me | solution 1 for GlobalTheory.KS.Endo.app_top_constFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:26:09.397281+00:00
-- url     : https://prove2.me/submissions/f70defe4-9e0f-41b1-9de6-3c9a4dc53062

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EntireAntilinearLatticePeriodsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnVerticalVectorFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerCommutesWithEndomorphism

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Endo
namespace GlobalTheory.KS.Endo
theorem _root_.solution {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (f : X ⟶ X) (hf : f ≫ p = p) (r : R) :
    (f.app ⊤).hom (constFn p ⊤ r) = resG X (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤) (constFn p ⊤ r) := by
  have aux : ∀ q : X ⟶ Sp R, q = p → ∀ e e', q.appLE ⊤ (f ⁻¹ᵁ ⊤) e = p.appLE ⊤ (f ⁻¹ᵁ ⊤) e' := by
    rintro q rfl e e'
    rfl
  have key : ∀ e, p.appLE ⊤ ⊤ e ≫ f.app ⊤ =
      p.appLE ⊤ ⊤ e ≫ X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤)).op := by
    intro e
    rw [Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE f, Scheme.Hom.appLE_comp_appLE]
    exact aux _ hf _ _
  unfold constFn
  exact congrArg (fun φ : Γ(Sp R, ⊤) ⟶ Γ(X, f ⁻¹ᵁ ⊤) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (key _)
end GlobalTheory.KS.Endo
