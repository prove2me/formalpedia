-- Prove2me | solution 1 for GlobalTheory.GenPush.exists_gen_of_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:33:03.925823+00:00
-- url     : https://prove2.me/submissions/a522f2f8-8172-4254-9c87-32ddc289eaea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorIsoExtendFromOpenContainingCharts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ext_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.GenPush
variable {X Y : Scheme.{0}}
private theorem gm_res_eq_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} {h : V ≤ U} (hy : f y ∈ V)
    (a : Γ(X, U)ˣ) : gm f y V (res h a) = gm f y U a := by
  apply Units.ext
  rw [← gs_unit f y V hy, ← gs_unit f y U (h hy)]
  exact gs_res f y h hy a.val
end GlobalTheory.GenPush
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.GenPush
variable {X Y : Scheme.{0}}
namespace GlobalTheory.GenPush
theorem _root_.solution (c : Y ⟶ X) [IsOpenImmersion c] (N : LB X) (hN : ∀ a, N.U a ≤ c.opensRange)
    (V : N.ι → Y.Opens) (hV : ∀ a y, c y ∈ N.U a → y ∈ V a) (s : ∀ a, Γ(Y, V a)ˣ)
    (hs : ∀ (y : Y) a b, c y ∈ N.U a → c y ∈ N.U b →
      gm (𝟙 Y) y (V a) (s a) = gm c y (N.U a ⊓ N.U b) (N.g a b) * gm (𝟙 Y) y (V b) (s b)) :
    ∃ t : N.Gen, t.IsGen := by
  have hW : ∀ a, c ⁻¹ᵁ N.U a ≤ V a := fun a y hy => hV a y hy
  choose b hb using fun a => exists_ext_unit c (c ⁻¹ᵁ N.U a) (res (hW a) (s a))
  have hE : ∀ a, N.U a ≤ c ''ᵁ (c ⁻¹ᵁ N.U a) := by
    intro a x hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range c := hN a hx
    exact ⟨y, hx, rfl⟩
  have key : ∀ (y : Y) a, c y ∈ N.U a → gm c y (c ''ᵁ (c ⁻¹ᵁ N.U a)) (b a) = gm (𝟙 Y) y (V a) (s a) := by
    intro y a ha
    have e := hb a Y (𝟙 Y) y (by simpa using ha)
    rw [Category.id_comp] at e
    rw [e, gm_res_eq_gm (𝟙 Y) y (by simpa using ha)]
  refine ⟨⟨fun a => res (hE a) (b a)⟩, ?_⟩
  unfold LB.Gen.IsGen
  intro a a'
  apply Units.ext
  apply fn_ext
  intro x hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range c := hN a hx.1
  have hx' : (𝟙 X) (c y) ∈ N.U a ⊓ N.U a' := by simpa using hx
  rw [gs_unit (𝟙 X) (c y) _ hx', gs_unit (𝟙 X) (c y) _ hx']
  congr 1
  apply gm_inj c y hx hx
  rw [map_mul, gm_res_eq_gm c y hx, gm_res_eq_gm c y hx.1, gm_res_eq_gm c y hx, gm_res_eq_gm c y hx.2,
    key y a hx.1, key y a' hx.2]
  exact hs y a a' hx.1 hx.2
end GlobalTheory.GenPush
