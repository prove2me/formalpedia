-- Prove2me | solution 1 for GlobalTheory.CountableFibres.exists_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:45.87614+00:00
-- url     : https://prove2.me/submissions/06c76ee3-0add-442b-ab3f-810144e17ba9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialEqZeroOfEventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CountableFibres
namespace GlobalTheory.CountableFibres
theorem _root_.solution {d : ℕ} {I : Type} (L : (Fin d → ℂ) →ₗ[ℂ] (I → ℂ))
    (hL : Function.Injective L) :
    ∃ a : Fin d → I, ∀ x, (∀ i, L x (a i) = 0) → x = 0 := by
  let φ : I → Module.Dual ℂ (Fin d → ℂ) := fun b => (LinearMap.proj b) ∘ₗ L
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ φ
  have : Finite κ := hli.finite
  let _ : Fintype κ := Fintype.ofFinite κ
  have hker : ∀ x, (∀ k, L x (a k) = 0) → x = 0 := by
    intro x hx
    apply hL
    rw [map_zero]
    funext b
    have hb : φ b ∈ Submodule.span ℂ (Set.range (φ ∘ a)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨b, rfl⟩
    have hle : Submodule.span ℂ (Set.range (φ ∘ a)) ≤
        LinearMap.ker (Module.Dual.eval ℂ (Fin d → ℂ) x) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hx k
    exact hle hb
  have h1 : Fintype.card κ ≤ d := by
    simpa using hli.fintype_card_le_finrank
  have h2 : d ≤ Fintype.card κ := by
    have : Function.Injective (LinearMap.funLeft ℂ ℂ a ∘ₗ L) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      exact hker x fun k => congrFun hx k
    simpa using LinearMap.finrank_le_finrank_of_injective this
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq (le_antisymm h1 h2)).symm
  refine ⟨a ∘ e, fun x hx => hker x fun k => ?_⟩
  simpa using hx (e.symm k)
end GlobalTheory.CountableFibres
