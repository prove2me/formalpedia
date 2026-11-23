-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.sval_pullOver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:19.088801+00:00
-- url     : https://prove2.me/submissions/2eec22fc-87ef-45a3-a4a0-6a4fba646fe4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}
variable (π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
variable {π} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
variable {π' : Y' ⟶ Spec (CommRingCat.of R')} {f : R →+* R'} {p : Y' ⟶ Y}
  (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)} (hφ : ∀ k, φ' k = p ≫ φ k)
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (s : SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y') {z : Z} {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (pullOver L ε hp hφ s) r z J = sval s (r ≫ p) z J := by
  rw [sval_of s (r ≫ p) z J (fun k => J (r ≫ φ' k)) (fun k => by rw [hφ, Category.assoc])]
  exact gs_pullFn hp _ _ r z (hJ.mem φ' r)
end GlobalTheory.FieldBaseChange
