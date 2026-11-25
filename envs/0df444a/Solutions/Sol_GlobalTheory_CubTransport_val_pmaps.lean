-- Prove2me | solution 1 for GlobalTheory.CubTransport.val_pmaps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:27:25.419031+00:00
-- url     : https://prove2.me/submissions/08443b1a-d748-40fc-a6e5-b5449c007326

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CubTransport
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.CubTransport
theorem _root_.solution {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  rw [val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hc])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))
end GlobalTheory.CubTransport
