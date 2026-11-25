-- Prove2me | solution 1 for GlobalTheory.OnePoint.one_geometric_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:13.790617+00:00
-- url     : https://prove2.me/submissions/b705b464-d948-4a3f-ae93-82b57b4a6cae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_exists_eq_C_of_isAlgebraic
import Theorems.Thm_GlobalTheory_OnePoint_isIso_reduction
import Theorems.Thm_GlobalTheory_OnePoint_exists_point_of_injective
import Theorems.Thm_GlobalTheory_OnePoint_exists_section_laurentSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution (K : Type u) [Field K] [PerfectField K] :
    (∀ (F : Scheme.{u}) [Nonempty F] (f : F ⟶ Spec (.of K)) [LocallyOfFiniteType f]
      (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω],
      (∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b) →
      IsIso (F.nilradical.subschemeι ≫ f)) ∧
    (∀ (X Y : Scheme.{u}) (κ : X ⟶ Y) [LocallyOfFiniteType κ],
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        Function.Injective fun a : Spec (.of Ω) ⟶ X ↦ a ≫ κ) →
      ∀ (K' : Type u) [Field K'] [Algebra K K'] (x : Spec (.of K') ⟶ X) (y : Spec (.of K) ⟶ Y),
        x ≫ κ = specAlg(K, K') ≫ y →
        ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₀ = x ∧ x₀ ≫ κ = y) ∧
    (∀ x : K⸨X⸩, IsAlgebraic K x → ∃ c : K, x = HahnSeries.C c) ∧
    (∀ (F : Scheme.{u}) (f : F ⟶ Spec (.of K)) [LocallyQuasiFinite f]
      (x : Spec (.of K⸨X⸩) ⟶ F), x ≫ f = specAlg(K, K⸨X⸩) →
      ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, K⸨X⸩) ≫ x₀ = x ∧ x₀ ≫ f = 𝟙 _) := by
  refine ⟨fun F _ f _ Ω _ _ _ h ↦ isIso_reduction f Ω h, fun X Y κ _ h K' _ _ x y hx ↦ ?_,
    fun x hx ↦ exists_eq_C_of_isAlgebraic hx, fun F f _ x hx ↦ ?_⟩
  · obtain ⟨x₀, h₁, h₂, -⟩ := exists_point_of_injective κ h K' x y hx
    exact ⟨x₀, h₁, h₂⟩
  · obtain ⟨x₀, h₁, h₂, -⟩ := exists_section_laurentSeries f x hx
    exact ⟨x₀, h₁, h₂⟩
end GlobalTheory.OnePoint
