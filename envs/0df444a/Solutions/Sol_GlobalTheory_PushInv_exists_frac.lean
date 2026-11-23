-- Prove2me | solution 1 for GlobalTheory.PushInv.exists_frac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:58.550081+00:00
-- url     : https://prove2.me/submissions/936ca853-9a44-448b-9bde-025094818716

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PushInvertibleOfDensePart
import Theorems.Thm_GlobalTheory_PushInv_gs_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.PushInv
open GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.PushInv
theorem _root_.solution {A : X.Opens} (hA : IsAffineOpen A) {y : X} (hy : y ∈ A) (κ : X.presheaf.stalk y) :
    ∃ a b : Γ(X, A), IsUnit (gs (𝟙 X) y A b) ∧ κ * gs (𝟙 X) y A b = gs (𝟙 X) y A a := by
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : A)
  have h := hA.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj (hA.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk ((⟨y, hy⟩ : A) : X)) κ
  refine ⟨a, b, ?_, ?_⟩
  · rw [gs_id y A hy]
    exact IsLocalization.map_units (X.presheaf.stalk ((⟨y, hy⟩ : A) : X)) b
  · rw [gs_id y A hy, gs_id y A hy]
    exact e
end GlobalTheory.PushInv
