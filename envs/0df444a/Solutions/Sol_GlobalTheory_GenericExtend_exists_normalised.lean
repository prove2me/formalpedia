-- Prove2me | solution 1 for GlobalTheory.GenericExtend.exists_normalised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:27.180794+00:00
-- url     : https://prove2.me/submissions/5f6d8178-5c7c-4277-9828-74cdbd856c56

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
import Theorems.Thm_GlobalTheory_GenericExtend_gm_res_pullU
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
theorem _root_.solution {X U P Q : Scheme.{0}} {N : LB P} (hN : N.IsLB) {j : U ⟶ X} {e : X ⟶ P}
    {J : Q ⟶ P} {π : Q ⟶ U} {eU : U ⟶ Q} (w : eU ≫ J = j ≫ e) (hπ : eU ≫ π = 𝟙 U)
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N J τ) {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : Compat N e ρ) : ∃ τ', Compat N J τ' ∧ ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (J ⁻¹ᵁ N.U a) (τ' a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a) := by
  have hw : ∀ x, J (eU x) = e (j x) := fun x ↦ by
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  have hle : ∀ a, j ⁻¹ᵁ e ⁻¹ᵁ N.U a ≤ eU ⁻¹ᵁ J ⁻¹ᵁ N.U a := fun a x hx ↦
    show J (eU x) ∈ N.U a from hw x ▸ hx
  let u : ∀ a, Γ(U, j ⁻¹ᵁ e ⁻¹ᵁ N.U a)ˣ := fun a ↦
    pullU j _ (ρ a) * (res (hle a) (pullU eU _ (τ a)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι), e (j (κ z)) ∈ N.U a →
      gm κ z _ (u a) = gm (κ ≫ j) z _ (ρ a) * (gm (κ ≫ eU) z _ (τ a))⁻¹ := fun Z κ z a ha ↦ by
    rw [map_mul, map_inv, gm_pull κ j z _ ha, gm_res_pullU κ eU z _ ha]
  obtain ⟨v, hv⟩ := glue_unit ⊤ (fun a ↦ j ⁻¹ᵁ e ⁻¹ᵁ N.U a) (fun _ ↦ le_top)
    (fun x _ ↦ Opens.mem_iSup.2 (exists_chart hN (e (j x)))) u fun a b x hx ↦ by
      rw [hu _ _ _ _ hx.1, hu _ _ _ _ hx.2, hρ _ (𝟙 U ≫ j) x a b hx.1 hx.2,
        hτ _ (𝟙 U ≫ eU) x a b (hle a hx.1) (hle b hx.2), Category.assoc, Category.assoc, w]
      rw [mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  have ht : ∀ a, J ⁻¹ᵁ N.U a ≤ π ⁻¹ᵁ ⊤ := fun _ _ _ ↦ trivial
  refine ⟨fun a ↦ res (ht a) (pullU π ⊤ v) * τ a, fun Z r z a b ha hb ↦ ?_, fun Z κ z a ha ↦ ?_⟩
  · rw [map_mul, map_mul, gm_res_pullU r π z (ht a) ha, gm_res_pullU r π z (ht b) hb, hτ Z r z a b ha hb,
      mul_left_comm]
  · rw [map_mul, gm_res_pullU (κ ≫ eU) π z (ht a) (hle a ha), Category.assoc, hπ, Category.comp_id,
      ← gm_res κ z (le_top : j ⁻¹ᵁ e ⁻¹ᵁ N.U a ≤ ⊤) ha, hv, hu _ _ _ _ ha, inv_mul_cancel_right]
end GlobalTheory.GenericExtend
