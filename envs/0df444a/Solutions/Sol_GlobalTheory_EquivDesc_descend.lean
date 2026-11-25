-- Prove2me | solution 1 for GlobalTheory.EquivDesc.descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:39:58.273066+00:00
-- url     : https://prove2.me/submissions/cf7a6d73-50a5-4250-8616-a32476fd81f8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Theorems.Thm_GlobalTheory_EquivDesc_unit_ext_of_flat
import Theorems.Thm_GlobalTheory_EquivDesc_val_eq_av
import Theorems.Thm_GlobalTheory_EquivDesc_act_comp
import Theorems.Thm_GlobalTheory_EquivDesc_exists_ratio
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.EquivDesc
variable {S : Scheme.{0}}
variable {G B H : Over S} [GrpObj G] [GrpObj B] [GrpObj H] {q : G ⟶ B} {i : H ⟶ G} [IsMonHom q] [IsMonHom i]
  {L : LB G.left} {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}
namespace GlobalTheory.EquivDesc
theorem _root_.solution [Flat q.left] [Surjective q.left] [QuasiCompact q.left] (hk : IsPullback i (toUnit _) q η[B])
    (hL : L.IsLB) (h : ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ ∃ e, InvGen q a V e) :
    ∃ (M : LB B.left) (w : LB.Iso L (M.pull q.left)), M.IsLB ∧ w.IsGen ∧
      ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J) (j : M.ι), Good L z J → q.left (x.left z) ∈ M.U j →
        gw w ((t ≫ i) * x).left z j (J ((t ≫ i) * x).left) * val a (lift t x).left z J = gw w x.left z j (J x.left) := by
  choose V hV e he using h
  choose m hm using fun b b' => exists_ratio hk hL (he b) (he b')
  let M : LB B.left := ⟨B.left, V, m⟩
  let w : LB.Iso L (M.pull q.left) := ⟨fun p => res (le_inf (fun _ hx => mem_pull.1 hx.1) inf_le_right :
    (M.pull q.left).U p.1 ⊓ L.U p.2 ≤ q.left ⁻¹ᵁ V (p.1 PUnit.unit) ⊓ L.U p.2) (e (p.1 PUnit.unit) p.2)⁻¹⟩
  have hw : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : M.ι) (k : L.ι), q.left (f y) ∈ V j → f y ∈ L.U k →
      gw w f y j k = (gm f y _ (e j k))⁻¹ := fun Y f y j k hj hk =>
    (gm_res f y _ (show f y ∈ (M.pull q.left).U (fun _ => j) ⊓ L.U k from ⟨mem_pull.2 hj, hk⟩) _).trans (map_inv _ _)
  have hm' : ∀ b b' y k, q.left y ∈ V b → q.left y ∈ V b' → y ∈ L.U k →
      gm q.left y _ (m b b') = gm (𝟙 _) y _ (e b' k) * (gm (𝟙 _) y _ (e b k))⁻¹ := fun b b' y k h₁ h₂ h₃ => by
    have := hm b b' _ (𝟙 _) y k h₁ h₂ h₃
    rwa [Category.id_comp] at this
  refine ⟨M, w, ⟨?_, fun b => unit_ext_of_flat q.left fun y hy => ?_,
    fun b b' b'' => unit_ext_of_flat q.left fun y hy => ?_⟩, (isGen_iff w).2 fun Y f y j j' k k' hj hj' hk hk' => ?_,
    fun T t x z J j hJ hj => ?_⟩
  · exact top_le_iff.1 fun b _ => Opens.mem_iSup.2 ⟨b, hV b⟩
  · obtain ⟨k, hk⟩ := exists_chart hL y
    rw [gm_res _ y _ hy, map_one]
    exact (hm' b b y k hy hy hk).trans (mul_inv_cancel _)
  · obtain ⟨k, hk⟩ := exists_chart hL y
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
    refine (congrArg₂ (· * ·) (hm' b b' y k hy.1.1 hy.1.2 hk) (hm' b' b'' y k hy.1.2 hy.2 hk)).trans
      (Eq.trans ?_ (hm' b b'' y k hy.1.1 hy.2 hk).symm)
    rw [mul_comm, _root_.mul_assoc, inv_mul_cancel_left]
  · have := hm j j' Y f y k' hj hj' hk'
    rw [hw Y f y j k hj hk, hw Y f y j' k' hj' hk', (he j).gen Y f y k k' hj hk hk']
    refine Eq.trans ?_ (congrArg (· * _ * _) this).symm
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have hj' : q.left (((t ≫ i) * x).left z) ∈ V j := (congrArg (fun m => m z ∈ V j) (act_comp hk t x)).mpr hj
    rw [hw _ _ z j _ hj' (hJ _), hw _ _ z j _ hj (hJ _), (he j).inv T t x z _ _ hj (hJ _) (hJ _), val_eq_av,
      mul_inv_rev, inv_mul_cancel_right]
end GlobalTheory.EquivDesc
