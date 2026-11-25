-- Prove2me | solution 1 for GlobalTheory.EquivDesc.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:04:41.827024+00:00
-- url     : https://prove2.me/submissions/da1f1afd-788f-4661-8a08-5619f8d47d09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Theorems.Thm_GlobalTheory_EquivDesc_gm_appLE
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_invariant_functions_descend
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
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
    (hL : L.IsLB) {V V' : B.left.Opens} {e e'} (he : InvGen q a V e) (he' : InvGen q a V' e') :
    ∃ m : Γ(B.left, V ⊓ V')ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (k : L.ι), q.left (f y) ∈ V →
      q.left (f y) ∈ V' → f y ∈ L.U k → gm (f ≫ q.left) y _ m = gm f y _ (e' k) * (gm f y _ (e k))⁻¹ := by
  let W : L.ι → G.left.Opens := fun k => q.left ⁻¹ᵁ (V ⊓ V') ⊓ L.U k
  have l₁ : ∀ k, W k ≤ q.left ⁻¹ᵁ V ⊓ L.U k := fun k y hy => ⟨hy.1.1, hy.2⟩
  have l₂ : ∀ k, W k ≤ q.left ⁻¹ᵁ V' ⊓ L.U k := fun k y hy => ⟨hy.1.2, hy.2⟩
  have hu : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (k : L.ι), f y ∈ W k →
      gm f y (W k) (res (l₂ k) (e' k) * (res (l₁ k) (e k))⁻¹) = gm f y _ (e' k) * (gm f y _ (e k))⁻¹ :=
    fun Y f y k h => by rw [map_mul, map_inv, gm_res f y _ h, gm_res f y _ h]
  obtain ⟨s, hs⟩ := glue_unit (q.left ⁻¹ᵁ (V ⊓ V')) W (fun _ => inf_le_left) (fun y hy => by
      obtain ⟨k, hk⟩ := exists_chart hL y
      exact Opens.mem_iSup.2 ⟨k, hy, hk⟩) (fun k => res (l₂ k) (e' k) * (res (l₁ k) (e k))⁻¹) (fun k k' y hy => by
      rw [hu _ (𝟙 _) y k hy.1, hu _ (𝟙 _) y k' hy.2, he.gen _ (𝟙 _) y k k' hy.1.1.1 hy.1.2 hy.2.2,
        he'.gen _ (𝟙 _) y k k' hy.1.1.2 hy.1.2 hy.2.2, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv])
  have hs' : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (k : L.ι), f y ∈ W k →
      gm f y _ s = gm f y _ (e' k) * (gm f y _ (e k))⁻¹ := fun Y f y k h =>
    (gm_res f y inf_le_left h s).symm.trans ((congrArg (gm f y (W k)) (hs k)).trans (hu Y f y k h))
  obtain ⟨-, d₂, d₃⟩ := invariant_functions_descend S G B H q i ‹_› ‹_› ‹_› ‹_› ‹_› hk (V ⊓ V')
  obtain ⟨m, hm⟩ := d₃ s.val fun Z t g h₁ h₂ => by
    refine congrArg Units.val (unit_ext (a := Units.map (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom.toMonoidHom s)
      (b := Units.map (g.left.appLE _ ⊤ h₂).hom.toMonoidHom s) fun z _ => ?_)
    obtain ⟨k₁, hk₁⟩ := exists_chart hL (((t ≫ i) * g).left z)
    obtain ⟨k₂, hk₂⟩ := exists_chart hL (g.left z)
    have m₂ : g.left z ∈ q.left ⁻¹ᵁ (V ⊓ V') := h₂ trivial
    rw [gm_appLE, gm_appLE, hs' _ _ z k₁ ⟨h₁ trivial, hk₁⟩, hs' _ _ z k₂ ⟨m₂, hk₂⟩, he.inv Z t g z k₁ k₂ m₂.1 hk₁ hk₂,
      he'.inv Z t g z k₁ k₂ m₂.2 hk₁ hk₂, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv]
  have um : IsUnit m := d₂ m (hm ▸ s.isUnit)
  have pm : pullU q.left _ um.unit = s := Units.ext hm
  refine ⟨um.unit, fun Y f y k h h' hk => ?_⟩
  rw [← gm_pull f q.left y (V ⊓ V') ⟨h, h'⟩, pm]
  exact hs' Y f y k ⟨⟨h, h'⟩, hk⟩
end GlobalTheory.EquivDesc
