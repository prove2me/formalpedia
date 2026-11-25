-- Prove2me | solution 1 for GlobalTheory.PrimeSection.exists_isUnit_res_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:31.856123+00:00
-- url     : https://prove2.me/submissions/5553941f-379d-4d46-8206-354dcf3025d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
variable [IsIntegral X]
variable {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
variable [IsLocallyNoetherian X]
include hη hp
namespace GlobalTheory.PrimeSection
theorem _root_.solution (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hru : ∀ a, IsUnit (r a)) {T : Scheme.{u}} [IsIntegral T] (e : T ⟶ X)
    (he : ∃ y', e y' ∈ X.basicOpen t) {y : T} (hy : e y ∉ X.basicOpen t) {a₀ : ι}
    (hya : e y ∈ U a₀) {u : Γ(T, e ⁻¹ᵁ U a₀)} (hu : IsUnit u)
    (hur : T.presheaf.map (homOfLE (e.preimage_mono inf_le_left)).op u =
      e.app (U a₀ ⊓ X.basicOpen t) (r a₀)) :
    ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) = r a := by
  obtain ⟨τ, hτ⟩ := exists_unit_eq_res t
  obtain ⟨n, s, hsu, hsc, hs⟩ := exists_zpow_mul_isUnit hη hp hU hg τ hτ hr hru
  suffices hn : n = 0 by
    subst hn
    refine ⟨s, hsu, hsc, fun a => ?_⟩
    rw [hs a, zpow_zero, Units.val_one, map_one, one_mul]

  have hTV : genericPoint T ∈ e ⁻¹ᵁ U a₀ := genericPoint_mem (show y ∈ e ⁻¹ᵁ U a₀ from hya)
  have hTD : genericPoint T ∈ e ⁻¹ᵁ X.basicOpen t := by
    obtain ⟨y', hy'⟩ := he
    exact genericPoint_mem (show y' ∈ e ⁻¹ᵁ X.basicOpen t from hy')
  have hψ : ∀ (W W' : X.Opens) (hWW : W' ≤ W) (h' : genericPoint T ∈ e ⁻¹ᵁ W') (f : Γ(X, W)),
      T.presheaf.germ _ (genericPoint T) h' (e.app W' (X.presheaf.map (homOfLE hWW).op f)) =
        T.presheaf.germ _ (genericPoint T) (e.preimage_mono hWW h') (e.app W f) := by
    intro W W' hWW h' f
    rw [← CommRingCat.comp_apply (X.presheaf.map (homOfLE hWW).op) (e.app W'), e.naturality, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  have hTVD : genericPoint T ∈ e ⁻¹ᵁ (U a₀ ⊓ X.basicOpen t) := ⟨hTV, hTD⟩
  let φ := (T.presheaf.germ _ (genericPoint T) hTD).hom.comp (e.app (X.basicOpen t)).hom
  refine zpow_eq_zero (T.presheaf.germ _ (genericPoint T) hTV).hom
    (germ_injective_of_isIntegral T _ hTV) (σ := e.app (U a₀) (s a₀)) (u := u)
    (p := e.app (U a₀) (X.presheaf.map (homOfLE (le_top : U a₀ ≤ ⊤)).op t))
    ((hsu a₀).map _) hu ?_ (Units.map φ.toMonoidHom τ) ?_ ?_
  ·
    intro hpu
    apply hy
    have hyb : y ∈ T.basicOpen (e.app (U a₀) (X.presheaf.map (homOfLE (le_top : U a₀ ≤ ⊤)).op t)) := by
      rw [T.basicOpen_of_isUnit hpu]
      exact hya
    rw [← Scheme.preimage_basicOpen, Scheme.basicOpen_res] at hyb
    exact hyb.2
  · change φ τ = _
    simp only [φ, RingHom.comp_apply]
    rw [hτ, hψ ⊤ (X.basicOpen t) le_top hTD t, hψ ⊤ (U a₀) le_top hTV t]
  · have h1 := congrArg (T.presheaf.germ _ (genericPoint T) hTVD) (congrArg (e.app _) (hs a₀))
    rw [hψ (U a₀) _ inf_le_left hTVD (s a₀), map_mul, map_mul, hψ (X.basicOpen t) _ inf_le_right hTVD,
      ← hur, TopCat.Presheaf.germ_res_apply] at h1
    rw [h1]
    congr 1
    change φ ↑(τ ^ n) = ((Units.map φ.toMonoidHom τ ^ n : _) : T.functionField)
    rw [← map_zpow]
    rfl
end GlobalTheory.PrimeSection
