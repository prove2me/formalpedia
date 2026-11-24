-- Prove2me | solution 1 for GlobalTheory.cotangent_relation_derivation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:44:55.838948+00:00
-- url     : https://prove2.me/submissions/560696d2-e085-4e38-8c7a-158bb5c86107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationSplitKaehlerDSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GenericResidueLinearIndependence
import Theorems.Thm_GlobalTheory_derivation_mem_of_mem_sq
import Theorems.Thm_GlobalTheory_residue_algebraMap_eq_zero_iff_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution {k A R : Type} [CommRing k] [CommRing A] [Algebra k A]
    (q : Ideal A) [q.IsPrime] [CommRing R] [IsLocalRing R] [Algebra A R]
    [IsLocalization.AtPrime R q]
    (δ : Derivation k A A) {κ : Type} (J : Finset κ) (g : κ → A)
    (hg : ∀ j, algebraMap A R (g j) ∈ maximalIdeal R) (c : κ → ResidueField R)
    (hrel : ∑ j ∈ J, c j • (maximalIdeal R).toCotangent ⟨_, hg j⟩ = 0) :
    ∑ j ∈ J, c j * residue R (algebraMap A R (δ (g j))) = 0 := by
  set ψ : A →+* ResidueField R := (residue R).comp (algebraMap A R) with hψdef
  have hψ : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => residue_algebraMap_eq_zero_iff_mem q x
  have hgq : ∀ j, g j ∈ q := fun j => (hψ _).1 ((residue_eq_zero_iff _).2 (hg j))
  set r : κ → R := fun j => (residue_surjective (c j)).choose with hr
  have hrc : ∀ j, residue R (r j) = c j := fun j => (residue_surjective (c j)).choose_spec
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples q.primeCompl J r
  have hb' : ∀ i ∈ J, ∃ x : A, algebraMap A R x = (b : A) • r i := fun i hi => hb i hi
  choose! a ha using hb'
  have hb0 : ψ b ≠ 0 := fun h => b.2 ((hψ _).1 h)
  have hψa : ∀ j ∈ J, ψ (a j) = ψ b * c j := by
    intro j hj
    simp only [hψdef, RingHom.comp_apply, ha j hj, Algebra.smul_def, map_mul, hrc]
  set y : A := ∑ j ∈ J, a j * g j with hy
  have hyq : y ∈ q := q.sum_mem fun j _ => q.mul_mem_left _ (hgq j)

  have hT : (maximalIdeal R).toCotangent
      (∑ j ∈ J, algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R)) = 0 := by
    rw [map_sum]
    have : ∀ j ∈ J, (maximalIdeal R).toCotangent (algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R))
        = ψ b • (c j • (maximalIdeal R).toCotangent ⟨_, hg j⟩) := by
      intro j hj
      rw [map_smul, smul_smul, ← hψa j hj]
      exact (algebraMap_smul (ResidueField R) (algebraMap A R (a j)) _).symm
    rw [Finset.sum_congr rfl this, ← Finset.smul_sum, hrel, smul_zero]
  rw [Ideal.toCotangent_eq_zero] at hT
  have hcoe : ((∑ j ∈ J, algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R) : maximalIdeal R) : R)
      = algebraMap A R y := by
    simp [hy, Submodule.coe_sum, map_sum, map_mul, Algebra.smul_def]
  rw [hcoe, ← IsLocalization.AtPrime.map_eq_maximalIdeal q R, ← Ideal.map_pow,
    IsLocalization.mem_map_algebraMap_iff q.primeCompl R] at hT
  obtain ⟨⟨x, s⟩, hxs⟩ := hT
  rw [← map_mul, IsLocalization.eq_iff_exists q.primeCompl R] at hxs
  obtain ⟨t, ht⟩ := hxs
  have hz : (t : A) * (y * s) ∈ q ^ 2 := ht ▸ Ideal.mul_mem_left _ _ x.2
  have hδz := (hψ _).2 (derivation_mem_of_mem_sq δ q hz)
  have hs0 : ψ s ≠ 0 := fun h => s.2 ((hψ _).1 h)
  have ht0 : ψ t ≠ 0 := fun h => t.2 ((hψ _).1 h)
  have hy0 : ψ y = 0 := (hψ _).2 hyq
  have hδy : ψ (δ y) = 0 := by
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hy0] at hδz
    simpa [hs0, ht0] using hδz
  have hg0 : ∀ j, ψ (g j) = 0 := fun j => (hψ _).2 (hgq j)
  rw [hy, map_sum, map_sum] at hδy
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hg0, zero_mul, add_zero] at hδy
  rw [Finset.sum_congr rfl (fun j hj => by rw [hψa j hj, mul_assoc]), ← Finset.mul_sum] at hδy
  exact (mul_eq_zero.1 hδy).resolve_left hb0
end GlobalTheory
