-- Prove2me | solution 1 for GlobalTheory.UU.SchurComp.sval_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:07:36.943897+00:00
-- url     : https://prove2.me/submissions/b142f236-d1f9-4bee-84b4-214fb6e9f692

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalRaw
import Theorems.Thm_GlobalTheory_UU_SchurComp_gs_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
namespace GlobalTheory.UU.SchurComp
theorem _root_.solution {n : ℕ} {s : LB.Sec (LB.LinComb L φ ε)} {b : Fin n → LB.Sec (LB.LinComb L φ ε)} (a : Fin n → Γ(Y, ⊤))
    (h : ∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (a i) * (b i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) : sval s r z J = ∑ i, gs r z ⊤ (a i) * sval (b i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ((gs_sum r z _ hm _).trans ?_)
  refine Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans ?_
  exact congrArg (· * _) (gs_res r z le_top hm _)
end GlobalTheory.UU.SchurComp
