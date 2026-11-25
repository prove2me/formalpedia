-- Prove2me | solution 1 for GlobalTheory.CubTransport.exists_pmaps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:40.917639+00:00
-- url     : https://prove2.me/submissions/d226f854-4360-4806-b354-bad6ef15f743

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Theorems.Thm_GlobalTheory_CubTransport_exists_down_units
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq


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
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  have key : ∀ (ψ : K → (Y' ⟶ X)) (_ : ∀ k, φ' k ≫ F = ψ k) (t₀ : LB.Gen (LB.LinComb L ψ ε)), t₀.IsGen →
      ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L ψ p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L ψ p) (t₀.s p) = pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
    intro ψ hψ t₀ h₀
    obtain rfl : (fun k => φ' k ≫ F) = ψ := funext hψ
    exact exists_down_units hw hL hL' t₀ h₀
  obtain ⟨a, ha, hv⟩ := key _ hc (LB.pullGen L φ ε t h) (pullGen_isGen _ _ _ _ ht h)
  refine ⟨a, ha, fun Z r z p q hp hq => ?_⟩
  have hm : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 fun k => by
    show φ k (h (r z)) ∈ L.U (p k)
    rw [pt_eq hc]; exact hp k
  refine Eq.trans ?_ (hv Z r z p q hm (Set.mem_iInter.2 hq))
  exact ((gm_res r z _ hm _).trans (gm_pull r h z (LB.wchart L φ p)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)).symm
end GlobalTheory.CubTransport
