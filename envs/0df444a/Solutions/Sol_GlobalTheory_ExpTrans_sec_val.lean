-- Prove2me | solution 1 for GlobalTheory.ExpTrans.sec_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:09.172938+00:00
-- url     : https://prove2.me/submissions/61ce5e11-b927-44f2-ae7c-fc410d3dbc25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
theorem _root_.solution (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L' φ' ε))
    (r : Z ⟶ Y') (z : Z)
    (H : ∀ (p : K → L.ι) (q : K → L'.ι), (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (s'.f q))
    {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sval s (r ≫ h) z J = (∏ κ, om w z J J' (r ≫ φ' κ) ^ ε κ).val * sval s' r z J' := by
  rw [sval_of s (r ≫ h) z J (fun κ => J ((r ≫ φ' κ) ≫ F))
    (fun κ => by rw [Category.assoc, Category.assoc, hc])]
  exact H _ (fun κ => J' (r ≫ φ' κ)) (fun κ => hJ ((r ≫ φ' κ) ≫ F)) (fun κ => hJ' (r ≫ φ' κ))
end GlobalTheory.ExpTrans
