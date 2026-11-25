-- Prove2me | solution 1 for GlobalTheory.SecPull.existsUnique_secPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:27:43.090483+00:00
-- url     : https://prove2.me/submissions/f5c23be5-1c15-4d1f-b575-02ea1128830f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Theorems.Thm_GlobalTheory_SecPull_exists_down_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecPull
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.SecPull
theorem _root_.solution (X X' Y Y' : Scheme.{0}) (L : LB X) (L' : LB X') (F : X' ⟶ X) (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) (K : Type) [Fintype K] (φ' : K → (Y' ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃! a : LB.Sec (LB.LinComb L' φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  obtain ⟨a, ha⟩ := exists_down_sec ((isGen_iff w).1 hw) hL hL' φ' φ ε h hc s
  refine ⟨a, fun Z r z p q hp hq => ?_, fun b hb => ?_⟩
  · rw [ha Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)]
    exact (Units.mul_inv_cancel_left (pw w φ' ε r z p q) _).symm
  · have e : b.f = a.f := funext fun q => fn_ext fun y hy => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      refine Eq.trans ?_ (ha _ (𝟙 Y') y p q (Set.mem_iInter.2 hp) hy).symm
      rw [hb _ (𝟙 Y') y p q hp (Set.mem_iInter.1 hy)]
      exact (Units.inv_mul_cancel_left (pw w φ' ε (𝟙 Y') y p q) _).symm
    cases a; cases b; cases e; rfl
end GlobalTheory.SecPull
