-- Prove2me | solution 1 for GlobalTheory.PushInv.spread
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:11.414743+00:00
-- url     : https://prove2.me/submissions/8ee95884-55b0-4d8d-95c0-0a1e1ca1cb04

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
import Theorems.Thm_GlobalTheory_PushInv_gs_id
import Theorems.Thm_GlobalTheory_PushInv_gs_sub
import Theorems.Thm_GlobalTheory_PushInv_exists_nhds_of_gs_eq
import Theorems.Thm_GlobalTheory_AbLocusPull_gs_secOn
import Theorems.Thm_GlobalTheory_AbLocusPull_isUnit_gs_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_appLE


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
theorem _root_.solution (π : Y ⟶ X) [GeometricallyIrreducible π] [IsReduced Y] (hπ : IsOpenMap π) {L : LB Y}
    {V W W' : X.Opens} {θ : ∀ i, Γ(Y, π ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (π ⁻¹ᵁ V))
    {s : ∀ i, Γ(Y, π ⁻¹ᵁ W ⊓ L.U i)} (hs : s ∈ secOn L (π ⁻¹ᵁ W)) (a : Γ(X, W')) (g : Y) (i : L.ι)
    (hV : π g ∈ V) (hW : π g ∈ W) (hW' : π g ∈ W') (hi : g ∈ L.U i)
    (e : gs (𝟙 Y) g _ (s i) = gs π g W' a * gs (𝟙 Y) g _ (θ i)) :
    ∃ O : X.Opens, π g ∈ O ∧ O ≤ W ∧ O ≤ W' ∧ ∀ k z, π z ∈ O → z ∈ L.U k →
      gs (𝟙 Y) z _ (s k) = gs π z W' a * gs (𝟙 Y) z _ (θ k) := by
  have pl : ∀ z, π z ∈ W' → gs (𝟙 Y) z (π ⁻¹ᵁ W') ((π.app W').hom a) = gs π z W' a := fun z hz => by
    rw [gs_pull (𝟙 Y) π z W' hz, Category.id_comp]
  rw [← pl g hW'] at e
  obtain ⟨N, hN, hle, eN⟩ := exists_nhds_of_gs_eq (U₁ := π ⁻¹ᵁ W ⊓ L.U i) (U₂ := π ⁻¹ᵁ W') (U₃ := π ⁻¹ᵁ V ⊓ L.U i)
    ⟨hW, hi⟩ hW' ⟨hV, hi⟩ _ _ _ e
  let O : X.Opens := ⟨π '' N, hπ _ N.2⟩
  have o₁ : O ≤ W := by rintro _ ⟨z, hz, rfl⟩; exact (hle hz).1.1.1
  have o₂ : O ≤ W' := by rintro _ ⟨z, hz, rfl⟩; exact (hle hz).1.2
  have o₃ : O ≤ V := by rintro _ ⟨z, hz, rfl⟩; exact (hle hz).2.1
  refine ⟨O, ⟨g, hN, rfl⟩, o₁, o₂, fun k z hz hk => ?_⟩
  let t : Γ(Y, π ⁻¹ᵁ O ⊓ L.U k) := resG Y (inf_le_inf_right _ (π.preimage_mono o₁)) (s k) -
    (π.appLE W' _ (inf_le_left.trans (π.preimage_mono o₂))).hom a *
      resG Y (inf_le_inf_right _ (π.preimage_mono o₃)) (θ k)
  have vt : ∀ z ∈ π ⁻¹ᵁ O ⊓ L.U k, gs (𝟙 Y) z _ t = gs (𝟙 Y) z _ (s k) - gs π z W' a * gs (𝟙 Y) z _ (θ k) :=
    fun z hz => by
      rw [gs_sub _ z _ hz, gs_mul _ z _ hz, gs_res _ z _ hz, gs_res _ z _ hz, gs_appLE _ _ _ _ _ z hz,
        Category.id_comp]
  have ht : t = 0 := by
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨y', hy', ey⟩ := (Y.basicOpen_le _ hy).1
    have irr : IsIrreducible (π ⁻¹' {π y}) := by
      rw [← π.range_fiberι, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ (π.fiberι _).continuous.continuousOn
    obtain ⟨q, -, hq, hq'⟩ := irr.2 N (Y.basicOpen t) N.2 (Y.basicOpen t).2 ⟨y', ey, hy'⟩ ⟨y, rfl, hy⟩
    have hm : q ∈ π ⁻¹ᵁ O ⊓ L.U k := Y.basicOpen_le _ hq'
    have hu := (isUnit_gs_iff (𝟙 Y) q _ hm t).2 hq'
    rw [vt q hm, gs_secOn hs (𝟙 Y) q k i (hle hq).1.1.1 hm.2 (hle hq).2.2,
      gs_secOn hθ (𝟙 Y) q k i (hle hq).2.1 hm.2 (hle hq).2.2, eN q hq, pl q (hle hq).1.2,
      mul_left_comm, sub_self] at hu
    exact (not_isUnit_zero hu).elim
  have hm : z ∈ π ⁻¹ᵁ O ⊓ L.U k := ⟨hz, hk⟩
  rw [← sub_eq_zero, ← vt z hm, ht, gs_id z _ hm, map_zero]
end GlobalTheory.PushInv
