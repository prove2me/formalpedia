-- Prove2me | solution 1 for GlobalTheory.PrimeSection.exists_zpow_mul_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:11.505426+00:00
-- url     : https://prove2.me/submissions/bd2cacc5-7fb5-43f7-b4f3-0d4d93c2fb38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_isUnit_of_isUnit_res
import Theorems.Thm_GlobalTheory_PrimeSection_mem_basicOpen_of_compatible
import Theorems.Thm_GlobalTheory_PrimeSection_existsUnique_zpow_mul

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
    (hru : ∀ a, IsUnit (r a)) :
    ∃ n : ℤ, ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
  obtain ⟨a₀, ha₀⟩ := hU η
  have hgD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hr0 : ∃ a, r a ≠ 0 := by
    refine ⟨a₀, fun h0 => ?_⟩
    have : Nonempty ↥(U a₀ ⊓ X.basicOpen t) := ⟨⟨genericPoint X, genericPoint_mem ha₀, hgD⟩⟩
    exact (hru a₀).ne_zero h0
  obtain ⟨n, ⟨s, hsc, hs, a', x', hx'D, hx's⟩, -⟩ := existsUnique_zpow_mul hη hp hU hg τ hτ hr hr0
  refine ⟨n, s, fun a => ?_, hsc, hs⟩
  refine isUnit_of_isUnit_res hη hp ?_ fun hηa => ?_
  · rw [hs a]
    exact ((τ ^ n).isUnit.map _).mul (hru a)
  · have hηs' : η ∈ X.basicOpen (s a') := ((hη x').mp hx'D).mem_open (X.basicOpen (s a')).isOpen hx's
    exact mem_basicOpen_of_compatible hg hsc hηa hηs'
end GlobalTheory.PrimeSection
