-- Prove2me | solution 1 for GlobalTheory.GroupGlue.isSemiAbelian_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:10:59.614437+00:00
-- url     : https://prove2.me/submissions/b42b62c9-a42a-4ca4-ab95-b51c49db72a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
import Theorems.Thm_GlobalTheory_GroupGlue_over_ext
import Theorems.Thm_GlobalTheory_GroupGlue_exists_rep
import Theorems.Thm_GlobalTheory_GroupGlue_rep_mul
import Theorems.Thm_GlobalTheory_GroupGlue_of_charts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.GroupGlue
variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})
variable {𝒰} {G : Over X} {H : ∀ i, Over (𝒰.X i)} {ψ : ∀ i, (H i).left ⟶ G.left}
variable [∀ i, GrpObj (H i)]
variable [GrpObj G]
namespace GlobalTheory.GroupGlue
theorem _root_.solution (h : ∀ i, IsGrpPullback (H i) G (𝒰.f i) (ψ i)) (hs : ∀ i, IsSemiAbelian (H i)) :
    IsSemiAbelian G := by
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := fun i => (h i).1
  have i1 : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget @Smooth
  have i2' := AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat.{0}
  have i2 := @HasAffineProperty.instIsZariskiLocalAtTarget _ _ i2'
  have i3 : IsZariskiLocalAtTarget @GeometricallyConnected.{0} :=
    GeometricallyConnected.eq_geometrically ▸ inferInstance
  have hcomm : ∀ (T : Over X) (x y : T ⟶ G), x * y = y * x := by
    intro T x y
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_rep hψ hu x
    obtain ⟨b, hb⟩ := exists_rep hψ hu y
    have := (hs i).comm
    rw [← rep_mul h hu ha hb, ← rep_mul h hu hb ha, _root_.mul_comm]
  exact { comm := ⟨by
            have e1 := hcomm _ (fst G G) (snd G G)
            have e2 : (β_ G G).hom = lift (snd G G) (fst G G) := by
              apply CartesianMonoidalCategory.hom_ext <;> simp
            rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e1
            rw [e2, ← e1]⟩,
          smooth := of_charts _ hψ fun i => (hs i).smooth,
          separated := of_charts _ hψ fun i => (hs i).separated,
          quasiCompact := @of_charts _ _ _ _ _ _ i2 hψ fun i => (hs i).quasiCompact,
          geomConnected := of_charts _ hψ fun i => (hs i).geomConnected,
          fibres := by
            intro Ω _ _ p
            obtain ⟨y0⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
            have hr : Set.range p ⊆ Set.range (𝒰.f (𝒰.idx (p y0))) := by
              rintro _ ⟨y, rfl⟩
              rw [Subsingleton.elim y y0]
              exact 𝒰.covers (p y0)
            obtain ⟨T⟩ := (hs (𝒰.idx (p y0))).fibres Ω (IsOpenImmersion.lift _ p hr)
            have h1 := (isGrpPullback_pullback (H (𝒰.idx (p y0))) (IsOpenImmersion.lift _ p hr)).comp
              (h (𝒰.idx (p y0)))
            rw [IsOpenImmersion.lift_fac] at h1
            obtain ⟨e, he, -⟩ := grpPullback_iso h1 (isGrpPullback_pullback G p)
            exact ⟨torusExtOfIso e T⟩ }
end GlobalTheory.GroupGlue
