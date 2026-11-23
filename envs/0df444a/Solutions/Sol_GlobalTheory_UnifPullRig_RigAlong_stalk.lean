-- Prove2me | solution 1 for GlobalTheory.UnifPullRig.RigAlong.stalk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:27.887544+00:00
-- url     : https://prove2.me/submissions/12fdfdcf-fb21-45bc-8d97-c1da1f7b4362

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CompatAlongOfSquare
import Theorems.Thm_GlobalTheory_UnifPullRig_gm_res_pull
import Theorems.Thm_GlobalTheory_UnifPullRig_pt_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
open GlobalTheory
open GlobalTheory.UnifPullRig
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S S' B B' T T' T₁ T₁' G G' A A' : Scheme.{0}}
variable {L : LB G} {M : LB A} {L' : LB G'} {M' : LB A'} {F : G' ⟶ G} {E : A' ⟶ A}
    {f : T ⟶ G} {p : T ⟶ A} {f' : T' ⟶ G'} {p' : T' ⟶ A'}
    {f₁ : T₁ ⟶ G} {p₁ : T₁ ⟶ A} {f₁' : T₁' ⟶ G'} {p₁' : T₁' ⟶ A'}
namespace GlobalTheory.UnifPullRig
namespace RigAlong
theorem _root_.solution {w : LB.Iso (L.pull f) (M.pull p)} {ε : S ⟶ T} {i : S ⟶ B} {eG : B ⟶ G}
    {eA : B ⟶ A} {rL : LB.Gen (L.pull eG)} {rM : LB.Gen (M.pull eA)} (H : RigAlong w ε i rL rM)
    (hf : ε ≫ f = i ≫ eG) (hp : ε ≫ p = i ≫ eA) {Z : Scheme.{0}} (r : Z ⟶ S) (z : Z) (jM : M.ι)
    (jL : L.ι) (hM : p (ε (r z)) ∈ M.U jM) (hL : f (ε (r z)) ∈ L.U jL) :
    gw w (r ≫ ε) z jM (fun _ => jL) * gm (r ≫ i) z ((L.pull eG).U (fun _ => jL)) (rL.s (fun _ => jL)) =
      gm (r ≫ i) z ((M.pull eA).U (fun _ => jM)) (rM.s (fun _ => jM)) := by
  have hz : r z ∈ ε ⁻¹ᵁ ((M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => jL)) ⊓
      (i ⁻¹ᵁ (L.pull eG).U (fun _ => jL) ⊓ i ⁻¹ᵁ (M.pull eA).U (fun _ => jM)) :=
    ⟨⟨mem_pull.2 hM, mem_pull.2 hL⟩, mem_pull.2 (pt_of_eq hf (r z) ▸ hL),
      mem_pull.2 (pt_of_eq hp (r z) ▸ hM)⟩
  have e := congrArg (gm r z _) (H (fun _ => jM, fun _ => jL) _ inf_le_left
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
  exact (congrArg₂ (· * ·) (gm_res_pull r ε z _ hz _) (gm_res_pull r i z _ hz _)).symm.trans
    ((map_mul _ _ _).symm.trans (e.trans (gm_res_pull r i z _ hz _)))
end RigAlong
end GlobalTheory.UnifPullRig
