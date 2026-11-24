-- Prove2me | solution 1 for GlobalTheory.SecGlue.exists_appLE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:36:56.671802+00:00
-- url     : https://prove2.me/submissions/d4cb421e-79f3-4552-9bd9-cb9204dff16e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {X Y Z : Scheme.{0}}
variable {J : Type} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]
namespace GlobalTheory.SecGlue
theorem _root_.solution (r : Z ⟶ X) [IsOpenImmersion r] {U : X.Opens} (hU : U ≤ r.opensRange)
    {W : Z.Opens} (h : W = r ⁻¹ᵁ U) (u : Γ(Z, W)) : ∃ w, (r.appLE U W h.le).hom w = u := by
  subst h
  have := r.isIso_app U hU
  rw [← r.app_eq_appLE]
  exact (ConcreteCategory.bijective_of_isIso (r.app U)).2 u
end GlobalTheory.SecGlue
