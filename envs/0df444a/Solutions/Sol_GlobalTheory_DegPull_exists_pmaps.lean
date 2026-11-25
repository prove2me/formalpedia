-- Prove2me | solution 1 for GlobalTheory.DegPull.exists_pmaps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:03.555813+00:00
-- url     : https://prove2.me/submissions/18153b47-87c1-4049-8a68-54296a2393bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Theorems.Thm_GlobalTheory_DegPull_exists_down_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pullGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DegPull
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.DegPull
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  obtain ⟨a, ha, hv⟩ := exists_down_val hw hL hL' hψ (LB.pullGen L φ ε t h) (DVR.pullGen_isGen _ _ _ _ ht h)
  refine ⟨a, ha, fun Z r z p q hp hq => ?_⟩
  have m : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 fun k => by
    show (h ≫ φ k) (r z) ∈ L.U (p k)
    rw [← hψ k]; exact hp k
  exact (gm_pullGen L φ ε t h r z p m).symm.trans (hv Z r z p q m (Set.mem_iInter.2 hq))
end GlobalTheory.DegPull
