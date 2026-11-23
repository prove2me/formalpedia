-- Prove2me | solution 1 for GlobalTheory.UnifPullRig.CompatAlong.stalk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:14:57.17054+00:00
-- url     : https://prove2.me/submissions/e3115965-c338-44d4-8aba-99a40e9bca0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CompatAlongOfSquare
import Theorems.Thm_GlobalTheory_UnifPullRig_gm_res_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
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
namespace CompatAlong
theorem _root_.solution {w₁ : LB.Iso (L.pull f₁) (M.pull p₁)} {w : LB.Iso (L.pull f) (M.pull p)}
    {m : T ⟶ T₁} (H : CompatAlong w₁ w m) (hf : m ≫ f₁ = f) (hp : m ≫ p₁ = p) {Z : Scheme.{0}}
    (r : Z ⟶ T) (z : Z) (jM : M.ι) (jL : L.ι) (hM : p (r z) ∈ M.U jM) (hL : f (r z) ∈ L.U jL) :
    gw w₁ (r ≫ m) z jM (fun _ => jL) = gw w r z jM (fun _ => jL) := by
  subst hf hp
  have hz : r z ∈ m ⁻¹ᵁ ((M.pull p₁).U (fun _ => jM) ⊓ (L.pull f₁).U (fun _ => jL)) ⊓
      ((M.pull (m ≫ p₁)).U (fun _ => jM) ⊓ (L.pull (m ≫ f₁)).U (fun _ => jL)) :=
    ⟨⟨mem_pull.2 hM, mem_pull.2 hL⟩, mem_pull.2 hM, mem_pull.2 hL⟩
  have e := congrArg (gm r z _) (H (fun _ => jM, fun _ => jL) _ inf_le_left inf_le_right)
  exact (gm_res_pull r m z _ hz _).symm.trans (e.trans (gm_res r z _ hz _))
end CompatAlong
end GlobalTheory.UnifPullRig
