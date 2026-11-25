-- Prove2me | solution 1 for GlobalTheory.KunnethDomain.sval_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:19.905032+00:00
-- url     : https://prove2.me/submissions/4535fd97-4d66-4943-a8c4-a9e9e346815f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecOfGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSmulEqSumMulOfIsDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
noncomputable section
open GlobalTheory
open GlobalTheory.KunnethDomain
open ReciprocityTheory.ChartRestriction.G.DVR
variable {X Y Y' T : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.KunnethDomain
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ} (s : Fin n → LB.Sec (LB.LinComb L φ ε))
    (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) : sval (secSum s) r z J = ∑ i, sval (s i) r z J := by
  have hm := hJ.mem φ r
  refine (gs_eq r z _ hm _).trans (Eq.trans ?_ (Finset.sum_congr rfl fun i _ => (gs_eq r z _ hm _).symm))
  exact map_sum ((T.presheaf.germ (r ⁻¹ᵁ LB.wchart L φ fun k => J (r ≫ φ k)) z hm).hom.comp
    (r.app (LB.wchart L φ fun k => J (r ≫ φ k))).hom) (fun i => (s i).f fun k => J (r ≫ φ k)) Finset.univ
end GlobalTheory.KunnethDomain
