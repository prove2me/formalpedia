-- Prove2me | solution 1 for GlobalTheory.UU.BoxSec.exists_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:37.745799+00:00
-- url     : https://prove2.me/submissions/af456873-696b-4e13-a1e3-b64614aef92d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RepSymInv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BoxSec
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)
variable {L Y}
namespace GlobalTheory.UU.BoxSec
theorem _root_.solution {K : Type} [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) {n : ℕ}
    (s : Fin n → LB.Sec (LB.LinComb L φ ε)) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left) (z : Z) (J), Good L z J →
      sval d r z J = ∑ i, sval (s i) r z J := by
  induction n with
  | zero =>
    refine ⟨DVR.SecOps.secZero, fun Z r z J hJ => ?_⟩
    rw [Fin.sum_univ_zero]
    exact (gs_eq r z _ (hJ.mem φ r) 0).trans (by rw [map_zero, map_zero])
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih (fun i => s i.succ)
    refine ⟨DVR.SecOps.secAdd (s 0) d, fun Z r z J hJ => ?_⟩
    rw [Fin.sum_univ_succ, ← hd Z r z J hJ]
    exact gs_add r z _ (hJ.mem φ r) _ _
end GlobalTheory.UU.BoxSec
