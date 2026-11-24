-- Prove2me | solution 1 for GlobalTheory.PrimeSection.existsUnique_zpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:51:56.979807+00:00
-- url     : https://prove2.me/submissions/5305d68a-9e19-4b3a-a0b9-d3b405852423

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_germ_res
import Theorems.Thm_GlobalTheory_PrimeSection_algebraMap_germ
import Theorems.Thm_GlobalTheory_PrimeSection_eq_of_germ_eq
import Theorems.Thm_GlobalTheory_PrimeSection_isDiscreteValuationRing_stalk
import Theorems.Thm_GlobalTheory_PrimeSection_exists_res_eq
import Theorems.Thm_GlobalTheory_PrimeSection_germ_eq_mul_germ
import Theorems.Thm_GlobalTheory_PrimeSection_compatible_of_res_eq
import Theorems.Thm_GlobalTheory_PrimeSection_mem_basicOpen_of_compatible
import Theorems.Thm_GlobalTheory_PrimeElement_existsUnique_zpow_mul_eq_unit


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
    (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(X, U a),
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a) ∧
      ∃ a, ∃ x, x ∉ X.basicOpen t ∧ x ∈ X.basicOpen (s a) := by
  have hgD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hηD : η ∉ X.basicOpen t := (hη η).mpr (specializes_refl η)
  obtain ⟨a₀, ha₀⟩ := hU η
  have hga₀ : genericPoint X ∈ U a₀ := genericPoint_mem ha₀

  have hf : X.presheaf.germ _ (genericPoint X) (⟨hga₀, hgD⟩ : genericPoint X ∈ U a₀ ⊓ X.basicOpen t) (r a₀) ≠ 0 := by
    intro hf0
    obtain ⟨b, hb⟩ := hr0
    apply hb
    refine eq_of_germ_eq fun hgb => ?_
    rw [map_zero, germ_eq_mul_germ hr hgb ⟨hga₀, hgD⟩, hf0, mul_zero]

  obtain ⟨hdvr, hirr⟩ := isDiscreteValuationRing_stalk hη hp
  have := hdvr

  have hφ : ∀ n : ℤ, X.presheaf.germ _ (genericPoint X) hgD (↑(τ ^ n) : Γ(X, X.basicOpen t)) =
      (algebraMap (X.presheaf.stalk η) X.functionField (X.presheaf.germ ⊤ η trivial t)) ^ n := by
    intro n
    have h1 : X.presheaf.germ _ (genericPoint X) hgD (τ : Γ(X, X.basicOpen t)) =
        algebraMap _ X.functionField (X.presheaf.germ ⊤ η trivial t) := by
      rw [hτ, germ_res, algebraMap_germ]
    rw [← h1]
    change ((Units.map (X.presheaf.germ _ (genericPoint X) hgD).hom.toMonoidHom (τ ^ n) : X.functionField)) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨n, ⟨u, hu, hun⟩, huniq⟩ :=
    GlobalTheory.PrimeElement.existsUnique_zpow_mul_eq_unit (K := X.functionField) hirr hf

  have hext : ∀ a, ∃ sa : Γ(X, U a), X.presheaf.map (homOfLE inf_le_left).op sa =
      X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
    intro a
    refine exists_res_eq hη hp _ fun hηa => ?_
    refine ⟨X.presheaf.germ _ η (⟨hηa, ha₀⟩ : η ∈ U a ⊓ U a₀) (g a a₀) * u, ?_⟩
    rw [map_mul, map_mul, hun, algebraMap_germ, germ_res, hφ n,
      germ_eq_mul_germ hr (⟨genericPoint_mem hηa, hgD⟩ : genericPoint X ∈ U a ⊓ X.basicOpen t) ⟨hga₀, hgD⟩]
    ring
  choose s hs using hext
  have hcomp := compatible_of_res_eq hgD hr (↑(τ ^ n) : Γ(X, X.basicOpen t)) hs
  refine ⟨n, ⟨s, hcomp, hs, a₀, η, hηD, ?_⟩, ?_⟩
  · rw [X.mem_basicOpen (s a₀) η ha₀]
    have hsu : X.presheaf.germ (U a₀) η ha₀ (s a₀) = u := by
      apply IsFractionRing.injective (X.presheaf.stalk η) X.functionField
      rw [hun, algebraMap_germ, ← germ_res inf_le_left (⟨hga₀, hgD⟩ : genericPoint X ∈ U a₀ ⊓ X.basicOpen t) (s a₀),
        hs a₀, map_mul, germ_res, hφ n]
    exact hsu ▸ hu
  · rintro n' ⟨s', hs'c, hs', a', x', hx'D, hx's⟩
    apply huniq n'
    have hηs' : η ∈ X.basicOpen (s' a') := ((hη x').mp hx'D).mem_open (X.basicOpen (s' a')).isOpen hx's
    have hηs₀ : η ∈ X.basicOpen (s' a₀) := mem_basicOpen_of_compatible hg hs'c ha₀ hηs'
    refine ⟨X.presheaf.germ (U a₀) η ha₀ (s' a₀), (X.mem_basicOpen _ η ha₀).mp hηs₀, ?_⟩
    rw [algebraMap_germ, ← germ_res inf_le_left (⟨hga₀, hgD⟩ : genericPoint X ∈ U a₀ ⊓ X.basicOpen t) (s' a₀),
      hs' a₀, map_mul, germ_res, hφ n']
end GlobalTheory.PrimeSection
