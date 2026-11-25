-- Prove2me | solution 1 for GlobalTheory.TwistLoc.exists_up_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:46:30.449093+00:00
-- url     : https://prove2.me/submissions/68b54199-79e6-491c-b457-53e9e0e533c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Theorems.Thm_GlobalTheory_TwistLoc_exists_sec_of_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pw_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory GlobalTheory.TwistLoc
variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.TwistLoc
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ψ : K → (Y ⟶ X)} (hψ : ∀ k, φ' k ≫ F = ψ k) (ε : K → ℤ)
    (a : LB.Sec (LB.LinComb L' φ' ε)) : ∃ s : LB.Sec (LB.LinComb L ψ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L ψ p → r z ∈ LB.wchart L' φ' q →
        gs r z (LB.wchart L ψ p) (s.f p) = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  obtain rfl : (fun k => φ' k ≫ F) = ψ := funext hψ
  choose u hu using fun p q => exists_pw w φ' ε p q
  let V : (K → L.ι) × (K → L'.ι) → Y.Opens := fun i =>
    LB.wchart L (fun k => φ' k ≫ F) i.1 ⊓ LB.wchart L' φ' i.2
  obtain ⟨v, hv⟩ : ∃ v : ∀ i, Γ(Y, V i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, r z ∈ V i →
      gs r z (V i) (v i) = (pw w φ' ε r z i.1 i.2).val * gs r z (LB.wchart L' φ' i.2) (a.f i.2) :=
    ⟨fun i => (u i.1 i.2).val * (Y.presheaf.map (homOfLE (inf_le_right : V i ≤ LB.wchart L' φ' i.2)).op).hom (a.f i.2),
      fun Z r z i hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
        ((gs_unit r z _ hz _).trans (congrArg Units.val (hu i.1 i.2 Z r z hz))) (gs_res r z _ hz _))⟩
  obtain ⟨s, hs⟩ := exists_sec_of_cover hL (fun k => φ' k ≫ F) ε V (fun y => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      choose q hq using fun k => exists_chart hL' (φ' k y)
      exact ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩) (fun i => i.1) (fun i => inf_le_left) v
    (fun i i' y hi hi' => by
      rw [hv _ _ y i hi, hv _ _ y i' hi', sec_trans a (𝟙 Y) y hi.2 hi'.2,
        pw_trans hw φ' ε (𝟙 Y) y hi.1 hi'.1 hi.2 hi'.2, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
        ← Units.val_mul, mul_right_comm _ _ (trF φ' ε (𝟙 Y) y i.2 i'.2), inv_mul_cancel_right])
  refine ⟨s, fun Z r z p q hp hq => ?_⟩
  rw [hs Z r z (p, q) p ⟨hp, hq⟩ hp, trF_self hL _ ε r z hp, Units.val_one, _root_.one_mul, hv Z r z (p, q) ⟨hp, hq⟩]
end GlobalTheory.TwistLoc
