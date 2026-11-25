-- Prove2me | solution 1 for GlobalTheory.PushInv.pushInvertible_of_densePart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:06.805106+00:00
-- url     : https://prove2.me/submissions/aaedc9c1-2a54-4b89-aba3-78f14e8671f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PushInvertibleOfDensePart
import Theorems.Thm_GlobalTheory_PushInv_gs_comp_stalkMap
import Theorems.Thm_GlobalTheory_PushInv_gs_id
import Theorems.Thm_GlobalTheory_PushInv_gs_specializes
import Theorems.Thm_GlobalTheory_PushInv_stalkMap_injective_of_flat
import Theorems.Thm_GlobalTheory_PushInv_stalkSpecializes_injective
import Theorems.Thm_GlobalTheory_PushInv_exists_ratio_above
import Theorems.Thm_GlobalTheory_PushInv_spread
import Theorems.Thm_GlobalTheory_PushInv_gs_eq_of_mul_eq
import Theorems.Thm_GlobalTheory_AbLocusPull_glue_fn
import Theorems.Thm_GlobalTheory_AbLocusPull_isUnit_gs_iff
import Theorems.Thm_GlobalTheory_forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth
import Theorems.Thm_GlobalTheory_genericPoints_subset_range_of_isDominant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_dvd_descend
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_stalkMap


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.PushInv
open GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.PushInv
theorem _root_.solution : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (G : Over X) (G₀ : Over U) (φ : G₀.left ⟶ G.left) (L : LB G.left) (L₀ : LB G₀.left), Smooth G.hom → GeometricallyIntegral G.hom → IsPullback φ G₀.hom G.hom j → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → PushInvertible G₀ L₀ → (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)) → PushInvertible G L := by
  intro X U _ j hX _ _ _ _ G G₀ φ L L₀ _ _ sq hL hL₀ hw h₀ H x
  obtain ⟨V, hx, θ, hθ, hne⟩ := H x
  refine ⟨V, hx, θ, hθ, fun W hW s hs => ?_, hne⟩
  have hG := forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hX
  have : IsReduced G.left := by
    have : ∀ g : G.left, _root_.IsReduced (G.left.presheaf.stalk g) := fun g =>
      have := (hG g).1
      inferInstance
    exact isReduced_of_isReduced_stalk _
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) sq.flip ‹_›
  have loc : ∀ y : W, ∃ (O : X.Opens) (a : Γ(X, O)), y.1 ∈ O ∧ O ≤ W ∧ ∀ k z, G.hom z ∈ O → z ∈ L.U k →
      gs (𝟙 _) z _ (s k) = gs G.hom z O a * gs (𝟙 _) z _ (θ k) := by
    rintro ⟨y, hy⟩
    obtain ⟨g, i, rfl, hg⟩ := hne y (hW hy)
    have := (hG g).1
    have hm : g ∈ G.hom ⁻¹ᵁ V ⊓ L.U i := G.left.basicOpen_le _ hg
    have hm' : g ∈ G.hom ⁻¹ᵁ W ⊓ L.U i := ⟨hy, hm.2⟩
    have hu := (isUnit_gs_iff (𝟙 _) g _ hm _).2 hg
    obtain ⟨ξ, hξ, hsp⟩ : ∃ ξ ∈ genericPoints X, ξ ⤳ G.hom g := by
      let C : irreducibleComponents X := ⟨_, irreducibleComponent_mem_irreducibleComponents (G.hom g)⟩
      exact ⟨(genericPoints.ofComponent C).1, (genericPoints.ofComponent C).2,
        (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent⟩
    obtain ⟨u, rfl⟩ := genericPoints_subset_range_of_isDominant j hξ
    obtain ⟨ν, hν, eν⟩ := Flat.generalizingMap G.hom hsp
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback sq ν u eν
    obtain ⟨A, hA, hgA, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := G.hom g) trivial
    have hsp' : G.hom (φ z) ⤳ G.hom g := hν.map G.hom.continuous
    have hzA : G.hom (φ z) ∈ A := hsp'.mem_open A.2 hgA
    obtain ⟨a, b, hb, e⟩ := exists_ratio_above sq.w hL hL₀ hw h₀ hA hθ hs z i hzA (hsp'.mem_open W.2 hy)
      (hν.mem_open (G.left.basicOpen _).2 hg)
    have tr : ∀ f : Γ(X, A), gs (φ ≫ G.hom) z A f =
        (φ.stalkMap z).hom ((G.left.presheaf.stalkSpecializes hν).hom (gs G.hom g A f)) := fun f => by
      rw [gs_comp_stalkMap _ _ z A hzA, gs_specializes G.hom hν A hgA]
    have tr' : ∀ (O : G.left.Opens) (f : Γ(G.left, O)), g ∈ O → gs φ z O f =
        (φ.stalkMap z).hom ((G.left.presheaf.stalkSpecializes hν).hom (gs (𝟙 _) g O f)) := fun O f hO => by
      rw [gs_stalkMap φ z O (hν.mem_open O.2 hO), gs_specializes (𝟙 _) hν O hO]
    have e' : gs G.hom g A b * gs (𝟙 _) g _ (s i) = gs G.hom g A a * gs (𝟙 _) g _ (θ i) := by
      apply stalkSpecializes_injective hν
      apply stalkMap_injective_of_flat φ z
      rw [map_mul, map_mul, map_mul, map_mul, ← tr, ← tr, ← tr' _ _ hm, ← tr' _ _ hm']
      exact e
    have hb0 : gs G.hom g A b ≠ 0 := fun h0 => by
      rw [tr, h0, map_zero, map_zero] at hb
      exact not_isUnit_zero hb
    have hd : gs G.hom g A b ∣ gs G.hom g A a := (hu.dvd_mul_right).1 ⟨_, e'.symm⟩
    have hd' := hd
    rw [gs_stalkMap G.hom g A hgA, gs_stalkMap G.hom g A hgA] at hd'
    obtain ⟨c, hc⟩ := dvd_descend G.hom g hd'
    obtain ⟨W', hW', c, rfl⟩ := X.presheaf.exists_germ_eq c
    rw [← gs_id _ W' hW'] at hc
    have ec : gs G.hom g A a = gs G.hom g A b * gs G.hom g W' c := by
      rw [gs_stalkMap G.hom g A hgA a, hc, map_mul, ← gs_stalkMap G.hom g A hgA, ← gs_stalkMap G.hom g W' hW']
    rw [ec, _root_.mul_assoc] at e'
    obtain ⟨O, hO, o₁, o₂, eO⟩ := spread G.hom G.hom.isOpenMap hθ hs c g i hm.1 hy hW' hm.2
      (mul_left_cancel₀ hb0 e')
    exact ⟨O, resG X o₂ c, hO, o₁, fun k z hz hk => by rw [gs_res _ z _ hz]; exact eO k z hz hk⟩
  choose O a hO hOW ea using loc
  obtain ⟨b, hb⟩ := glue_fn W O hOW (fun y hy => ⟨⟨y, hy⟩, hO _⟩) a (fun p q y hp hq => by
    obtain ⟨g, i, rfl, hg⟩ := hne y (hW (hOW p hp))
    have hm : g ∈ G.hom ⁻¹ᵁ V ⊓ L.U i := G.left.basicOpen_le _ hg
    exact gs_eq_of_mul_eq G.hom _ _ g hp hq ((isUnit_gs_iff (𝟙 _) g _ hm _).2 hg)
      ((ea p i g hp hm.2).symm.trans (ea q i g hq hm.2)))
  have val : ∀ (c : Γ(X, W)) i z (hz : z ∈ G.hom ⁻¹ᵁ W ⊓ L.U i), gs (𝟙 _) z _
      ((G.hom.appLE W (G.hom ⁻¹ᵁ W ⊓ L.U i) inf_le_left).hom c *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hW)) (θ i)) =
      gs G.hom z W c * gs (𝟙 _) z _ (θ i) := fun c i z hz => by
    rw [gs_mul _ z _ hz, gs_res _ z _ hz, gs_appLE _ _ _ _ _ z hz, Category.id_comp]
  refine existsUnique_of_exists_of_unique ⟨b, fun i => fn_ext fun z hz => ?_⟩ fun c c' hc hc' => fn_ext fun y hy => ?_
  · rw [val b i z hz, ea ⟨G.hom z, hz.1⟩ i z (hO _) hz.2, gs_stalkMap G.hom z W hz.1,
      hb _ ⟨G.hom z, hz.1⟩ (hO _), ← gs_stalkMap G.hom z _ (hO ⟨G.hom z, hz.1⟩)]
  · obtain ⟨g, i, rfl, hg⟩ := hne y (hW hy)
    have hm : g ∈ G.hom ⁻¹ᵁ V ⊓ L.U i := G.left.basicOpen_le _ hg
    have hm' : g ∈ G.hom ⁻¹ᵁ W ⊓ L.U i := ⟨hy, hm.2⟩
    refine gs_eq_of_mul_eq G.hom _ _ g hy hy ((isUnit_gs_iff (𝟙 _) g _ hm _).2 hg) ?_
    rw [← val c i g hm', ← val c' i g hm', ← hc i, ← hc' i]
end GlobalTheory.PushInv
