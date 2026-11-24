-- Prove2me | solution 1 for GlobalTheory.exists_pseudoBasis_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:00.200987+00:00
-- url     : https://prove2.me/submissions/45955dfa-84c4-478e-a67b-c7b6337313cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Theorems.Thm_GlobalTheory_exists_pseudoCoords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (I : Submodule E (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ (s : ℕ) (e : Module.Basis (Fin r) E (Fin r → E)) (c : Fin r → FractionalIdeal (𝓞 E)⁰ E), (∀ a, c a ≠ 0) ∧ (∀ v, v ∈ Λ ↔ ∀ a, e.repr v a ∈ c a) ∧ ∀ v, v ∈ I ↔ ∀ a : Fin r, s ≤ (a : ℕ) → e.repr v a = 0 := by
  intro E _ _ r Λ I hfg hsp
  obtain ⟨s, f, c, hf, hc, hΛ, hI⟩ :=
    exists_pseudoCoords (R := 𝓞 E) (K := E) r (Fin r → E) (by simp) Λ I hfg hsp
  have hinj : Function.Injective (LinearMap.pi f) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact hf v fun a => congrFun hv a
  let φ : (Fin r → E) ≃ₗ[E] (Fin r → E) := LinearEquiv.ofInjectiveEndo _ hinj
  have hφ : ∀ v a, (Module.Basis.ofEquivFun φ).repr v a = f a v := by
    intro v a
    rw [Module.Basis.ofEquivFun_repr_apply]
    rfl
  refine ⟨s, Module.Basis.ofEquivFun φ, c, hc, ?_, ?_⟩
  · simpa only [hφ] using hΛ
  · simpa only [hφ] using hI
end GlobalTheory
