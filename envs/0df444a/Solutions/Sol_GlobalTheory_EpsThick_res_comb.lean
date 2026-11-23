-- Prove2me | solution 1 for GlobalTheory.EpsThick.res_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:23:45.925022+00:00
-- url     : https://prove2.me/submissions/f4964ee4-68b3-49b1-a97d-fe3d2659a97d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure

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
open GlobalTheory GlobalTheory.EpsThick
variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {π : Y' ⟶ Sp (DualNumber R)} {ρ : Y' ⟶ Y}
namespace GlobalTheory.EpsThick
theorem _root_.solution {U O : Y.Opens} (h : U ≤ O) (ab : Γ(Y, O) × Γ(Y, O)) :
    (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom (comb π ρ O ab) =
      comb π ρ U ((Y.presheaf.map (homOfLE h).op).hom ab.1, (Y.presheaf.map (homOfLE h).op).hom ab.2) := by
  have h1 : ∀ a, (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom ((ρ.app O).hom a) =
      (ρ.app U).hom ((Y.presheaf.map (homOfLE h).op).hom a) := fun a =>
    (congrArg (fun φ => φ.hom a) (ρ.naturality (homOfLE h).op)).symm
  have h2 : (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom (constFn π _ DualNumber.eps) =
      constFn π (ρ ⁻¹ᵁ U) DualNumber.eps := by
    exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of (DualNumber R))).inv.hom DualNumber.eps))
      (π.appLE_map (U := ⊤) (V := ρ ⁻¹ᵁ O) le_top (homOfLE (ρ.preimage_mono h)).op)
  simp only [comb, map_add, map_mul, h1, h2]
end GlobalTheory.EpsThick
