-- Prove2me | solution 1 for GlobalTheory.WeilIsogeny.exists_gen_of_lbPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:10.380029+00:00
-- url     : https://prove2.me/submissions/c7a73ab3-0e83-4f8f-a2dc-eebafa8618f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenMovePow
import Theorems.Thm_GlobalTheory_WeilIsogeny_wchart_le_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilIsogeny
open CommutatorPairing
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}
namespace GlobalTheory.WeilIsogeny
theorem _root_.solution (d : ℕ) (hε : ∀ k, ε' k = ε k * d) (a : LB.Gen (LB.LinComb (lbPow L d) φ ε))
    (ha : a.IsGen) : ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
        gm r z (LB.wchart L φ j) (u.s j) = gm r z (LB.wchart (lbPow L d) φ (fun k _ => j k)) (a.s fun k _ => j k) := by
  refine ⟨⟨fun j => res (wchart_le_pow d j) (a.s fun k _ => j k)⟩, fun j j' => unit_ext fun y hy => ?_,
    fun Z r z j hj => gm_res r z _ hj _⟩
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L φ ε' (𝟙 Y) y j j' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm))
  refine (gen_trans ha (𝟙 Y) y (wchart_le_pow d j hy.1) (wchart_le_pow d j' hy.2)).trans (congrArg (· * _) ?_)
  refine Finset.prod_congr rfl fun k _ => ?_
  have e := gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (d : ℤ)) (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.2 k)
  rw [Fintype.prod_unique, Category.comp_id] at e
  refine (congrArg (· ^ ε k) e).trans ?_
  rw [hε, mul_comm (ε k), zpow_mul]
end GlobalTheory.WeilIsogeny
