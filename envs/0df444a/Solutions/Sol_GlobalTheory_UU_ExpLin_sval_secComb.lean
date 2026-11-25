-- Prove2me | solution 1 for GlobalTheory.UU.ExpLin.sval_secComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:56:30.841746+00:00
-- url     : https://prove2.me/submissions/70cb0cad-ac7c-42ea-8775-114307ed35aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalSecComb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_lin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ExpLin
namespace GlobalTheory.UU.ExpLin
theorem _root_.solution {X Y T Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {n : ℕ} (p : Y ⟶ T) (c : Fin n → Γ(T, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (secComb (fun i => p.appTop.hom (c i)) t) r z J = ∑ i, gs (r ≫ p) z ⊤ (c i) * sval (t i) r z J := by
  rw [DVR.SectionScalarValuation.sval_lin (s := secComb (fun i => p.appTop.hom (c i)) t) (fun i => p.appTop.hom (c i)) t
    (fun _ => rfl) r z hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_pull r p z ⊤ trivial (c i))
end GlobalTheory.UU.ExpLin
