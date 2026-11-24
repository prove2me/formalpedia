-- Prove2me | solution 1 for GlobalTheory.PushInv.exists_ratio_above
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:56:32.973721+00:00
-- url     : https://prove2.me/submissions/39eadb6b-7eae-4e78-8726-89375cd09391

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
import Theorems.Thm_GlobalTheory_PushInv_exists_frac
import Theorems.Thm_GlobalTheory_PushInv_exists_secOn_pull_germ
import Theorems.Thm_GlobalTheory_AbLocusPull_isUnit_gs_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
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
theorem _root_.solution {U : Scheme.{0}} {j : U ⟶ X} [IsPreimmersion j] {G : Over X} {G₀ : Over U}
    {φ : G₀.left ⟶ G.left} {L : LB G.left} {L₀ : LB G₀.left} (sq : φ ≫ G.hom = G₀.hom ≫ j) (hL : L.IsLB)
    (hL₀ : L₀.IsLB) (hw : LBIso L₀ (L.pull φ)) (h₀ : PushInvertible G₀ L₀) {V W A : X.Opens} (hA : IsAffineOpen A)
    {θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (G.hom ⁻¹ᵁ V))
    {s : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ L.U i)} (hs : s ∈ secOn L (G.hom ⁻¹ᵁ W))
    (z : G₀.left) (i : L.ι) (hzA : G.hom (φ z) ∈ A) (hzW : G.hom (φ z) ∈ W)
    (hz : φ z ∈ G.left.basicOpen (θ i)) :
    ∃ a b : Γ(X, A), IsUnit (gs (φ ≫ G.hom) z A b) ∧
      gs (φ ≫ G.hom) z A b * gs φ z _ (s i) = gs (φ ≫ G.hom) z A a * gs φ z _ (θ i) := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨V₀, hV₀, θ₀, -, gen, -⟩ := h₀ (G₀.hom z)
  obtain ⟨k, hk⟩ := exists_chart hL₀ z
  have hm : φ z ∈ G.hom ⁻¹ᵁ V ⊓ L.U i := G.left.basicOpen_le _ hz
  have pt : ∀ y, G.hom (φ y) = j (G₀.hom y) := fun y => by
    rw [← Scheme.Hom.comp_apply, sq, Scheme.Hom.comp_apply]
  have hjA : j (G₀.hom z) ∈ A := pt z ▸ hzA
  have key : ∀ (W : X.Opens) (s : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ L.U i)), s ∈ secOn L (G.hom ⁻¹ᵁ W) →
      G.hom (φ z) ∈ W → ∃ a b : Γ(X, A), IsUnit (gs (φ ≫ G.hom) z A b) ∧
        gs (φ ≫ G.hom) z A b * gs φ z _ (s i) =
          gs (φ ≫ G.hom) z A a * ((gw w (𝟙 _) z i k).val * gs (𝟙 _) z _ (θ₀ k)) := by
    intro W s hs hzW
    have hle : G₀.hom ⁻¹ᵁ (V₀ ⊓ j ⁻¹ᵁ W) ≤ φ ⁻¹ᵁ (G.hom ⁻¹ᵁ W) := fun y hy => by
      show G.hom (φ y) ∈ W
      rw [pt]; exact hy.2
    have hu : G₀.hom z ∈ V₀ ⊓ j ⁻¹ᵁ W := ⟨hV₀, show j (G₀.hom z) ∈ W from pt z ▸ hzW⟩
    obtain ⟨s', hs', es⟩ := exists_secOn_pull_germ hL hL₀ w hw hle hs
    obtain ⟨c, hc, -⟩ := gen _ inf_le_left s' hs'
    have hz' : z ∈ G₀.hom ⁻¹ᵁ (V₀ ⊓ j ⁻¹ᵁ W) ⊓ L₀.U k := ⟨hu, hk⟩
    have e := congrArg (gs (𝟙 _) z _) (hc k)
    rw [es k z i hu hk hm.2, gs_mul _ z _ hz', gs_appLE _ _ _ _ _ z hz', gs_res _ z _ hz', Category.id_comp] at e
    obtain ⟨κ, hκ⟩ := j.stalkMap_surjective (G₀.hom z) (gs (𝟙 U) (G₀.hom z) _ c)
    obtain ⟨a, b, hb, eab⟩ := exists_frac hA hjA κ
    have tr : ∀ f : Γ(X, A), gs (φ ≫ G.hom) z A f =
        (G₀.hom.stalkMap z).hom ((j.stalkMap (G₀.hom z)).hom (gs (𝟙 X) (j (G₀.hom z)) A f)) := fun f => by
      rw [sq, gs_comp_stalkMap _ _ z A hjA, gs_stalkMap j _ A hjA]
    have e' : gs G₀.hom z _ c * gs (φ ≫ G.hom) z A b = gs (φ ≫ G.hom) z A a := by
      rw [tr, tr, ← eab, map_mul, map_mul, gs_stalkMap G₀.hom z _ hu, ← hκ]
    refine ⟨a, b, ?_, ?_⟩
    · rw [tr]; exact (hb.map _).map _
    · rw [Units.inv_mul_eq_iff_eq_mul] at e
      rw [e, ← e']; ring
  obtain ⟨a, b, hb, e⟩ := key W s hs hzW
  obtain ⟨a', b', hb', e'⟩ := key V θ hθ hm.1
  have ha' : IsUnit (gs (φ ≫ G.hom) z A a') :=
    isUnit_of_mul_isUnit_left (e' ▸ hb'.mul ((isUnit_gs_iff φ z _ hm _).2 hz))
  have hzA' : (φ ≫ G.hom) z ∈ A := hzA
  refine ⟨a * b', b * a', ?_, ?_⟩
  · rw [gs_mul _ z _ hzA']; exact hb.mul ha'
  · rw [gs_mul _ z _ hzA', gs_mul _ z _ hzA']
    linear_combination gs (φ ≫ G.hom) z A a' * e - gs (φ ≫ G.hom) z A a * e'
end GlobalTheory.PushInv
