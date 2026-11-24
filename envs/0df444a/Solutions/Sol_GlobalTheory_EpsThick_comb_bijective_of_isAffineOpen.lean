-- Prove2me | solution 1 for GlobalTheory.EpsThick.comb_bijective_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:04:42.778831+00:00
-- url     : https://prove2.me/submissions/50ba684a-29fb-4953-8441-688c4553c737

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Theorems.Thm_GlobalTheory_EpsThick_existsUnique_of_isPushout

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
theorem _root_.solution (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R))))
    {U : Y.Opens} (hU : IsAffineOpen U) : Function.Bijective (comb π ρ U) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine existsUnique_of_isPushout
    ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appLE ⊤ U (fun _ _ => trivial)).hom (ρ.app U)
    ((Scheme.ΓSpecIso (.of (DualNumber R))).inv ≫ π.appLE ⊤ (ρ ⁻¹ᵁ U) (fun _ _ => trivial)).hom ?_
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber R))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp
end GlobalTheory.EpsThick
