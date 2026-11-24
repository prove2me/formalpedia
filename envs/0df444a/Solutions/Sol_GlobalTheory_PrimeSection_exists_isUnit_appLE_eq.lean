-- Prove2me | solution 1 for GlobalTheory.PrimeSection.exists_isUnit_appLE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:23.478984+00:00
-- url     : https://prove2.me/submissions/08134584-f38c-4172-bf61-77224a7d7092

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Theorems.Thm_GlobalTheory_PrimeSection_res_appLE
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_res
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_appLE
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_injective
import Theorems.Thm_GlobalTheory_PrimeSection_exists_transport
import Theorems.Thm_GlobalTheory_PrimeSection_exists_unit_eq_res
import Theorems.Thm_GlobalTheory_PrimeSection_exists_zpow_mul_isUnit
import Theorems.Thm_GlobalTheory_PrimeSection_zpow_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
  [IsIntegral X] [IsLocallyNoetherian X]
  {Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] (hj : j.opensRange = X.basicOpen t)
  {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
  {W : ι → Y.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
include hη hp hj
namespace GlobalTheory.PrimeSection
theorem _root_.solution (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    {r : ∀ a, Γ(Y, W a)}
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (hru : ∀ a, IsUnit (r a)) {T T' : Scheme.{u}} [IsIntegral T] [Nonempty T'] (e : T ⟶ X)
    (k : T' ⟶ T) [IsOpenImmersion k] (e' : T' ⟶ Y) (he : e' ≫ j = k ≫ e)
    {y : T} (hy : e y ∉ X.basicOpen t) {a₀ : ι} {A : T.Opens} (hyA : y ∈ A)
    (hA : A ≤ e ⁻¹ᵁ U a₀) {A' : T'.Opens} (hA' : A' = k ⁻¹ᵁ A) (hA'' : A' ≤ e' ⁻¹ᵁ W a₀)
    {u : Γ(T, A)} (hu : IsUnit u) (hur : k.appLE A A' hA'.le u = e'.appLE (W a₀) A' hA'' (r a₀)) :
    ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, j.appLE (U a) (W a) (hW a).le (s a) = r a := by
  obtain ⟨τ, hτ⟩ : IsUnit (j.appTop t) := by
    obtain ⟨τ', hτ'⟩ := exists_unit_eq_res t
    have htop : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ X.basicOpen t := fun y _ ↦ hj.le ⟨y, rfl⟩
    have := τ'.isUnit.map (j.appLE _ ⊤ htop).hom
    rw [hτ', appLE_res] at this
    rwa [← show j.appLE ⊤ ⊤ _ = j.appTop from j.appLE_eq_app]
  obtain ⟨r', τ', hτ', hr', -, hu', H⟩ := exists_transport hj hW r hr τ hτ
  obtain ⟨n, s, hsu, hc, hs⟩ :=
    exists_zpow_mul_isUnit hη hp hU hg τ' hτ' hr' fun a ↦ hu' a (hru a)
  simp only [H] at hs
  have hnat : ∀ z : Γ(X, U a₀), k.appLE A A' hA'.le (e.appLE _ A hA z) =
      e'.appLE (W a₀) A' hA'' (j.appLE _ _ (hW a₀).le z) := fun z ↦ by
    have h : A' ≤ (k ≫ e) ⁻¹ᵁ U a₀ := hA'.le.trans (k.preimage_mono hA)
    rw [appLE_appLE k e rfl _ _ h, appLE_appLE e' j he _ _ h]
  let φ : Γ(Y, ⊤) →+* Γ(T', A') :=
    (e'.appLE (W a₀) A' hA'').hom.comp (Y.presheaf.map (homOfLE le_top).op).hom
  obtain rfl : n = 0 := by
    refine zpow_eq_zero (k.appLE A A' hA'.le).hom (appLE_injective k hA')
      ((hsu a₀).map (e.appLE _ A hA).hom) hu
      (p := e.appLE _ A hA (X.presheaf.map (homOfLE (le_top : U a₀ ≤ ⊤)).op t)) (fun H ↦ hy ?_)
      (Units.map φ.toMonoidHom τ) ?_ ?_
    · have := T.basicOpen_of_isUnit H
      rw [Scheme.basicOpen_appLE, Scheme.basicOpen_res] at this
      exact (show y ∈ A ⊓ e ⁻¹ᵁ (U a₀ ⊓ X.basicOpen t) from this.ge hyA).2.2
    · rw [hnat, appLE_res, Units.coe_map, hτ,
        ← show j.appLE ⊤ ⊤ le_top = j.appTop from j.appLE_eq_app]
      exact congrArg (e'.appLE (W a₀) A' hA'') (res_appLE j _ _ _)
    · rw [hnat, hs, map_mul, hur, ← map_zpow, Units.coe_map]
      rfl
  exact ⟨s, hsu, hc, fun a ↦ by simpa using hs a⟩
end GlobalTheory.PrimeSection
