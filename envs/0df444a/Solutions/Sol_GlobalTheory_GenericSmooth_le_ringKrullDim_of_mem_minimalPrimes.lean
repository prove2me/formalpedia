-- Prove2me | solution 1 for GlobalTheory.GenericSmooth.le_ringKrullDim_of_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:17:33.467284+00:00
-- url     : https://prove2.me/submissions/958cd771-e4f0-4ce0-88e3-db83d46132de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGenericFibreOfIndependentAndTangentBound

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.GenericSmooth
namespace GlobalTheory.GenericSmooth
theorem _root_.solution (o k R S : Type) [CommRing o] [IsDomain o] [Field k]
    [CommRing R] [CommRing S] [Algebra o k] [IsFractionRing o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    [IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S]
    [Algebra.FiniteType k S] (d : ℕ)
    (h : ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R →
      (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y)
    (q : Ideal S) (hq : q ∈ minimalPrimes S) : (d : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ q) := by
  have hp : q.IsPrime := hq.1.1
  let K := FractionRing (S ⧸ q)
  let ψ : S →ₐ[o] K := (IsScalarTower.toAlgHom o (S ⧸ q) K).comp (Ideal.Quotient.mkₐ o q)
  let φ : R →ₐ[o] K := ψ.comp (IsScalarTower.toAlgHom o R S)
  have hψ : ∀ s, ψ s = 0 ↔ s ∈ q := fun s ↦ by
    change algebraMap (S ⧸ q) K (Ideal.Quotient.mk q s) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ q) K), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker φ = q.under R := by
    ext r
    exact hψ (algebraMap R S r)
  have hmin : RingHom.ker φ ∈ minimalPrimes R := by
    have h' := IsLocalization.minimalPrimes_map
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S ⊥
    rw [Ideal.map_bot] at h'
    rw [hker]
    exact h'.le hq
  have hs : ∀ s : S, ∃ a b, φ b ≠ 0 ∧ ψ s = φ a / φ b := fun s ↦ by
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) s
    have hb : φ b ≠ 0 := ((IsLocalization.map_units S b).map ψ).ne_zero
    refine ⟨a, b, hb, ?_⟩
    rw [eq_div_iff hb]
    have := congrArg ψ hab
    rw [map_mul] at this
    exact this
  have hsurj : ∀ z : K, ∃ a b, z = φ a / φ b := fun z ↦ by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ q) z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, b, hb, h₁⟩ := hs x
    obtain ⟨a', b', hb', h₂⟩ := hs y
    refine ⟨a * b', b * a', ?_⟩
    change ψ x / ψ y = _
    rw [h₁, h₂, map_mul, map_mul, div_div_div_eq]
  obtain ⟨y, hy⟩ := h K φ hmin hsurj
  obtain ⟨n, h₁, h₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k (S ⧸ q)
  have hk : AlgebraicIndependent k y := by
    have : Algebra.IsAlgebraic o k := IsLocalization.isAlgebraic k (nonZeroDivisors o)
    exact hy.extendScalars k
  have h₃ := hk.cardinalMk_le_trdeg
  have : Algebra.IsAlgebraic (S ⧸ q) K := IsLocalization.isAlgebraic K (nonZeroDivisors (S ⧸ q))
  have : FaithfulSMul k (S ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k (S ⧸ q)).injective
  rw [← trdeg_add_eq k (S ⧸ q) (A := K), trdeg_eq_zero (R := S ⧸ q) (A := K), add_zero, h₂,
    Cardinal.mk_fin] at h₃
  rw [h₁]
  exact_mod_cast h₃
end GlobalTheory.GenericSmooth
