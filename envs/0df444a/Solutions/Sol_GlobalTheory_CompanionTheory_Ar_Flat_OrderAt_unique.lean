-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.OrderAt.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:42.690116+00:00
-- url     : https://prove2.me/submissions/15215f38-ba55-4dfc-b507-fbd5c372dddd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_ZUnit_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_ZUnit_of_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]
variable {L : Lat ξ E} {σ : E} {ϖ : Ω} {M M' : ℕ} {a a' : ℤ} {p : Cpt ξ}
namespace GlobalTheory.CompanionTheory.Ar.Flat
namespace OrderAt
theorem _root_.solution (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ regAt ξ p) (hp : ¬ Ar.unitAt ξ p ϖ) (ha : OrderAt L σ ϖ M a p)
    (ha' : OrderAt L σ ϖ M a' p) : a = a' := by
  obtain ⟨e, c, he, hL, hσ, ha⟩ := ha
  replace ha' := ha'.unitAt hL hσ
  have key : ∀ a b : ℤ, Ar.unitAt ξ p (c ^ M / ϖ ^ a) → Ar.unitAt ξ p (c ^ M / ϖ ^ b) → ¬ a < b := by
    intro a b ha hb hlt
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + ((n + 1 : ℕ) : ℤ) := ⟨(b - a - 1).toNat, by omega⟩
    have hc : c ^ M ≠ 0 := fun h => ha.1 (by rw [h, zero_div])
    have hu := ZUnit.mul ha (ZUnit.inv hb)
    have : c ^ M / ϖ ^ a * (c ^ M / ϖ ^ (a + ((n + 1 : ℕ) : ℤ)))⁻¹ = ϖ ^ (n + 1) := by
      have : ϖ ^ a ≠ 0 := zpow_ne_zero a h0
      rw [zpow_add₀ h0, zpow_natCast]
      field_simp
    rw [this] at hu
    exact hp (ZUnit.of_pow hϖ n.succ_ne_zero hu)
  exact le_antisymm (not_lt.1 (key a' a ha' ha)) (not_lt.1 (key a a' ha ha'))
end OrderAt
end GlobalTheory.CompanionTheory.Ar.Flat
