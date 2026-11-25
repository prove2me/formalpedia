-- Prove2me | solution 1 for GlobalTheory.GenericExtend.exists_isGen_of_densePart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:51:13.795491+00:00
-- url     : https://prove2.me/submissions/6f1161a6-24ee-45e9-9646-3f6301e0c812

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_GlobalTheory_GenericExtend_coheight_apply_le_one
import Theorems.Thm_GlobalTheory_GenericExtend_exists_specializes_mem_range
import Theorems.Thm_GlobalTheory_GenericExtend_exists_app_eq
import Theorems.Thm_GlobalTheory_GenericExtend_exists_compat
import Theorems.Thm_GlobalTheory_GenericExtend_exists_normalised
import Theorems.Thm_GlobalTheory_GenericExtend_extAt_of_coheight_eq_one
import Theorems.Thm_GlobalTheory_DvrModel_isLocallyNoetherian
import Theorems.Thm_GlobalTheory_isNormalScheme_of_smooth
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend
namespace GlobalTheory.GenericExtend
theorem _root_.solution : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (P : Over X) (e : X ⟶ P.left) (N : LB P.left), e ≫ P.hom = 𝟙 X → Smooth P.hom → GeometricallyIntegral P.hom → N.IsLB → (∃ r : (N.pull e).Gen, r.IsGen) → (∃ t : (N.pull (pullback.fst P.hom j)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro X U _ j hX _ _ _ _ P e N he _ _ hN ⟨r, hr⟩ ⟨t, ht⟩
  have := IsNormalScheme.of_pred hX
  have := isNormalScheme_of_smooth P.hom
  have := LocallyOfFiniteType.isLocallyNoetherian P.hom
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst P.hom j).app_injective
  obtain ⟨τ₀, hτ₀⟩ := exists_compat t ht
  obtain ⟨ρ, hρ⟩ := exists_compat r hr
  let eU : U ⟶ pullback P.hom j := pullback.lift (j ≫ e) (𝟙 U) (by simp [he])
  have w : eU ≫ pullback.fst P.hom j = j ≫ e := pullback.lift_fst _ _ _
  have hπ : eU ≫ pullback.snd P.hom j = 𝟙 U := pullback.lift_snd _ _ _
  obtain ⟨τ, hτ, hτρ⟩ := exists_normalised hN w hπ hτ₀ hρ
  have key : ∀ a, ∀ y ∈ N.U a, Order.coheight y ≤ 1 → y ∉ Set.range (pullback.fst P.hom j) →
      ExtAt (pullback.fst P.hom j) (N.U a) (τ a).val y ∧
        ExtAt (pullback.fst P.hom j) (N.U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j P.hom he hN w hπ hτ hτρ y
      (le_antisymm (coheight_apply_le_one P.hom h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (P.hom y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show P.hom y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst P.hom j).app _).hom _ = ((pullback.fst P.hom j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  let σ : ∀ a, Γ(P.left, N.U a)ˣ := fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩
  have hσ : ∀ a, pullU (pullback.fst P.hom j) _ (σ a) = τ a := fun a ↦ Units.ext (hs a)
  refine ⟨⟨σ⟩, fun a b ↦ Units.map_injective
    (f := ((pullback.fst P.hom j).app (N.U a ⊓ N.U b)).hom.toMonoidHom) (hJ _) ?_⟩
  change pullU _ _ _ = pullU _ _ _
  refine unit_ext fun q hq ↦ ?_
  have := hτ _ (𝟙 _) q a b hq.1 hq.2
  rw [← hσ, ← hσ, gm_pull _ _ q _ hq.1, gm_pull _ _ q _ hq.2] at this
  rw [gm_pull _ _ q _ hq, gm_pull _ _ q _ hq, map_mul, gm_res _ q _ hq, gm_res _ q _ hq]
  exact this
end GlobalTheory.GenericExtend
