-- Prove2me | solution 1 for GlobalTheory.ExpTrans.gen_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:05.345812+00:00
-- url     : https://prove2.me/submissions/2258ab7c-0e8b-493b-b01d-167bf2c69700

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.ExpTrans
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {X X' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
variable (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
  (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
namespace GlobalTheory.ExpTrans
theorem _root_.solution (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L' φ' ε))
    (H : PMaps w φ' φ ε t' t h) (z : Y') {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t h z J = (∏ κ, om w z J J' (φ' κ) ^ ε κ) * val t' (𝟙 _) z J' := by
  have := H _ (𝟙 _) z (fun κ => J (φ' κ ≫ F)) (fun κ => J' (φ' κ)) (fun κ => hJ (φ' κ ≫ F)) (fun κ => hJ' (φ' κ))
  simp only [Category.id_comp] at this
  rw [val_of t h z J (fun κ => J (φ' κ ≫ F)) (fun κ => by rw [hc]),
    val_of t' (𝟙 _) z J' (fun κ => J' (φ' κ)) (fun κ => by rw [Category.id_comp])]
  exact this
end GlobalTheory.ExpTrans
