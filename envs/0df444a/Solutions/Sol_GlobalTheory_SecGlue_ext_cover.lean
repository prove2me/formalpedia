-- Prove2me | solution 1 for GlobalTheory.SecGlue.ext_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:13.0668+00:00
-- url     : https://prove2.me/submissions/9101b1ca-dbef-44f4-9914-c3f6249988a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
import Theorems.Thm_GlobalTheory_SecGlue_gs_inj

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
theorem _root_.solution (hc : ∀ x : X, ∃ i y, a i y = x) {V : X.Opens} {s t : Γ(X, V)}
    (h : ∀ i y, a i y ∈ V → gs (a i) y V s = gs (a i) y V t) : s = t :=
  fn_ext fun x hx => by
    obtain ⟨i, y, rfl⟩ := hc x
    exact gs_inj (a i) y hx hx (h i y hx)
end GlobalTheory.SecGlue
