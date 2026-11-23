-- Prove2me | solution 1 for GlobalTheory.LocLift.HasLifts.lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:26:44.975419+00:00
-- url     : https://prove2.me/submissions/8c31c9fa-f3e4-47cb-b7e1-a4664fdaf904

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Theorems.Thm_GlobalTheory_LocLift_isHolTo_comp
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
omit [GrpObj G]
namespace GlobalTheory.LocLift
namespace HasLifts
theorem _root_.solution {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} (h : HasLifts B y e) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {W : Set V} {β : V → (Fin m → ℂ)} (x : ∀ w, Over.mk (y (β w)) ⟶ G)
    {w₀ : V} {z₀ : Fin g → ℂ} (hW : IsOpen W) (hw₀ : w₀ ∈ W) (hβ : DifferentiableOn ℂ β W)
    (hm : Set.MapsTo β W B) (hx : IsHolTo W (fun w => (x w).left)) (h0 : e (β w₀) z₀ = x w₀) :
    ∃ ζ : V → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w := by
  let φ : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨u₀, rfl⟩ := φ.symm.surjective w₀
  have hW' : IsOpen (φ.symm ⁻¹' W) := hW.preimage φ.symm.continuous
  obtain ⟨ζ, h1, h2, h3⟩ := h _ (φ.symm ⁻¹' W) (fun u => β (φ.symm u)) (fun u => x (φ.symm u)) u₀ z₀ hW' hw₀
    (hβ.comp φ.symm.differentiableOn fun _ hu => hu) (fun _ hu => hm hu)
    (isHolTo_comp hx hW' φ.symm.differentiableOn fun _ hu => hu) h0
  refine ⟨fun w => ζ (φ w), by simpa using h1, ?_, ?_⟩
  · exact AnalyticAt.comp_of_eq h2 (φ.toContinuousLinearMap.analyticAt (φ.symm u₀)) (by simp)
  · have ht : map φ.symm (𝓝 u₀) = 𝓝 (φ.symm u₀) := φ.symm.toHomeomorph.map_nhds_eq u₀
    rw [← ht, eventually_map]
    simpa only [φ.apply_symm_apply] using h3
end HasLifts
end GlobalTheory.LocLift
