-- Prove2me | solution 1 for GlobalTheory.algebraicIndependent_residue_iff_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:13.276258+00:00
-- url     : https://prove2.me/submissions/139a8060-25ea-47a3-a510-0e15382cdadb

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraicIndependentResidueIffGauss
import Theorems.Thm_GlobalTheory_residue_valuationSubring_ne_zero_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
open MvPolynomial
private theorem residue_eval₂_comap {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) (p : MvPolynomial σ (v.valuationSubring.comap f)) :
    letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
    IsLocalRing.residue v.valuationSubring
        (MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f)
          (fun s => ⟨t s, ht s⟩) p) =
      MvPolynomial.aeval (fun s => IsLocalRing.residue v.valuationSubring ⟨t s, ht s⟩)
        (MvPolynomial.map (IsLocalRing.residue (v.valuationSubring.comap f)) p) := by
  letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
  congr 1
private theorem coe_eval₂_comapInclusion_eq_eval₂_map {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) (p : MvPolynomial σ (v.valuationSubring.comap f)) :
    ((MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f)
          (fun s => (⟨t s, ht s⟩ : v.valuationSubring)) p : v.valuationSubring) : U) =
      MvPolynomial.eval₂ f t (MvPolynomial.map (v.valuationSubring.comap f).subtype p) := by
  rw [MvPolynomial.eval₂_map]
  exact MvPolynomial.eval₂_comp_left v.valuationSubring.subtype _ _ p
private theorem residue_comap_ne_zero_iff_valuation_eq_one {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (c : v.valuationSubring.comap f) :
    IsLocalRing.residue (v.valuationSubring.comap f) c ≠ 0 ↔ v (f c) = 1 := by
  have h := residue_valuationSubring_ne_zero_iff v (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f c)
  rw [← IsLocalRing.ResidueField.map_residue, map_ne_zero] at h
  exact h
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution (F U : Type) [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) :
    (letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
     AlgebraicIndependent (IsLocalRing.ResidueField (v.valuationSubring.comap f))
      (fun s => IsLocalRing.residue v.valuationSubring ⟨t s, ht s⟩)) ↔
    ∀ p : MvPolynomial σ F, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) →
      v (MvPolynomial.eval₂ f t p) = 1 := by
  letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
  rw [algebraicIndependent_iff]
  constructor
  · intro hind p hle hone
    obtain ⟨q, rfl⟩ : p ∈ Set.range (MvPolynomial.map (v.valuationSubring.comap f).subtype) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨α, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
      exact ⟨⟨p.coeff α, ValuationSubring.mem_comap.mpr ((v.mem_valuationSubring_iff _).mpr (hle α))⟩, rfl⟩
    obtain ⟨α, hα⟩ := hone
    rw [MvPolynomial.coeff_map] at hα
    rw [← coe_eval₂_comapInclusion_eq_eval₂_map f v σ t ht q, ← residue_valuationSubring_ne_zero_iff, residue_eval₂_comap]
    intro h0
    have hq := congrArg (MvPolynomial.coeff α) (hind _ h0)
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at hq
    exact (residue_comap_ne_zero_iff_valuation_eq_one f v (q.coeff α)).mpr hα hq
  · intro hg r hr
    by_contra hne
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective r
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hne
    rw [MvPolynomial.coeff_map] at hα
    have hle : ∀ β, v (f ((MvPolynomial.map (v.valuationSubring.comap f).subtype q).coeff β)) ≤ 1 := by
      intro β
      rw [MvPolynomial.coeff_map]
      exact (v.mem_valuationSubring_iff _).mp (ValuationSubring.mem_comap.mp (q.coeff β).2)
    have h1 := hg _ hle ⟨α, by
      rw [MvPolynomial.coeff_map]
      exact (residue_comap_ne_zero_iff_valuation_eq_one f v (q.coeff α)).mp hα⟩
    rw [← coe_eval₂_comapInclusion_eq_eval₂_map f v σ t ht q, ← residue_valuationSubring_ne_zero_iff, residue_eval₂_comap] at h1
    exact h1 hr
end GlobalTheory
