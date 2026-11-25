-- Prove2me | solution 1 for GlobalTheory.RegularQuotient.quotient_span_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:10:04.14483+00:00
-- url     : https://prove2.me/submissions/89f69fca-f022-44c2-b5bf-0b2bfa88d607

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuotientSpanRange
import Theorems.Thm_GlobalTheory_RegularQuotient_quot_regular
import Theorems.Thm_GlobalTheory_RegularQuotient_exists_extend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open IsLocalRing Matrix
namespace GlobalTheory.RegularQuotient
open IsLocalRing Matrix in
private theorem linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq (A : Type) [CommRing A]
    [IsRegularLocalRing A] (k : ℕ) (x : Fin k → A) (hx : ∀ i, x i ∈ maximalIdeal A)
    (hind : ∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) :
    LinearIndependent (ResidueField A)
      (fun i => (maximalIdeal A).toCotangent (⟨x i, hx i⟩ : maximalIdeal A)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha using fun j => IsLocalRing.residue_surjective (g j)
  have hmem : (∑ j, a j * x j) ∈ maximalIdeal A :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hx j)
  have hsum : (∑ j, a j * x j) ∈ maximalIdeal A ^ 2 := by
    rw [← Ideal.toCotangent_eq_zero (maximalIdeal A) ⟨_, hmem⟩]
    have he : (⟨∑ j, a j * x j, hmem⟩ : maximalIdeal A) =
        ∑ j, a j • (⟨x j, hx j⟩ : maximalIdeal A) := by
      ext; simp [Submodule.coe_sum, smul_eq_mul]
    rw [he, map_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← ha j, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  rw [← ha i, IsLocalRing.residue_eq_zero_iff]
  exact hind a hsum i
end GlobalTheory.RegularQuotient
end

set_option autoImplicit false
open IsLocalRing Matrix
open GlobalTheory GlobalTheory.RegularQuotient
open IsLocalRing Matrix
namespace GlobalTheory.RegularQuotient
namespace _root_.GlobalTheory.RegularQuotient
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (d k : ℕ)
    (x : Fin k → A),
    ringKrullDim A = ((d + k : ℕ) : WithBot ℕ∞) → (∀ i, x i ∈ maximalIdeal A) →
    (∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) →
    IsRegularLocalRing (A ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (A ⧸ Ideal.span (Set.range x)) = (d : WithBot ℕ∞) := by
  intro A _ _ d k x hd hx hind
  obtain ⟨J, _, t, hspan, hdim⟩ := _root_.GlobalTheory.RegularQuotient.exists_extend A
    (fun i => (⟨x i, hx i⟩ : maximalIdeal A))
    (linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq A k x hx hind)
  have hJ : Fintype.card J = d := by
    rw [hd, Fintype.card_fin] at hdim
    have h : d + k = Fintype.card J + k := by exact_mod_cast hdim
    omega
  have hspan' : Ideal.span (Set.range t ∪ Set.range x) = maximalIdeal A := hspan
  have hdim' : ringKrullDim A = ((Fintype.card J + Fintype.card (Fin k) : ℕ) : ℕ) := by
    rw [hd, Fintype.card_fin, hJ]
  obtain ⟨hreg, -, -, hq⟩ := _root_.GlobalTheory.RegularQuotient.quot_regular A t x hspan' hdim'
  exact ⟨hreg, by rw [hq, hJ]⟩
end _root_.GlobalTheory.RegularQuotient
end GlobalTheory.RegularQuotient
