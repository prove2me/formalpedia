-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.natCast_le_encard_zeroSetIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:30:01.953161+00:00
-- url     : https://prove2.me/submissions/e793df99-105c-45d7-8179-4fa99a5ca6b6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton
open TopologicalSpace
variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]
namespace GlobalTheory.CompanionTheory.FSCrofton
theorem _root_.solution [T2Space X] [SecondCountableTopology X] (A : Set X)
    (b : α → X → ℂ) (C : Fin d → α → ℂ) (N : ℕ) :
    (N : ℕ∞) ≤ (zeroSetIn A b C).encard ↔
      ∃ f : Fin N → countableBasis X,
        (∀ i j, i ≠ j → Disjoint (f i : Set X) (f j)) ∧
        ∀ i, ∃ z ∈ A ∩ (f i : Set X), ∀ k, ∑ j, C k j * b j z = 0 := by
  classical
  constructor
  · intro hN
    obtain ⟨t, htZ, htN⟩ := Set.exists_subset_encard_eq hN
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htN
    haveI : Finite t := htfin.to_subtype
    have hcard : Nat.card t = N := by
      rw [Nat.card_coe_set_eq, Set.ncard_def, htN, ENat.toNat_natCast]
    let e : t ≃ Fin N := (Finite.equivFin t).trans (finCongr hcard)
    obtain ⟨U, hU, hdisj⟩ := htfin.t2_separation
    have hex : ∀ i : Fin N, ∃ v ∈ countableBasis X, (e.symm i : X) ∈ v ∧ v ⊆ U (e.symm i) :=
      fun i => (isBasis_countableBasis X).exists_subset_of_mem_open (hU _).1 (hU _).2
    choose v hvB hpv hvU using hex
    refine ⟨fun i => ⟨v i, hvB i⟩, ?_, ?_⟩
    · intro i j hij
      have hne : (e.symm i : X) ≠ e.symm j := by
        intro h
        exact hij (e.symm.injective (Subtype.ext h))
      show Disjoint (v i) (v j)
      exact Disjoint.mono (hvU i) (hvU j) (hdisj (e.symm i).2 (e.symm j).2 hne)
    · intro i
      have hz : (e.symm i : X) ∈ zeroSetIn A b C := htZ (e.symm i).2
      simp only [zeroSetIn, Set.mem_ofPred_eq] at hz
      exact ⟨e.symm i, ⟨hz.1, hpv i⟩, hz.2⟩
  · rintro ⟨f, hdisj, hz⟩
    choose z hzmem hzero using hz
    have hinj : Function.Injective z := by
      intro i j h
      by_contra hij
      have hzj : z i ∈ (f j : Set X) := by
        rw [h]
        exact (hzmem j).2
      exact Set.disjoint_left.mp (hdisj i j hij) (hzmem i).2 hzj
    have hsub : ((Finset.univ.image z : Finset X) : Set X) ⊆ zeroSetIn A b C := by
      intro x hx
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
      obtain ⟨i, rfl⟩ := hx
      simp only [zeroSetIn, Set.mem_ofPred_eq]
      exact ⟨(hzmem i).1, hzero i⟩
    calc (N : ℕ∞) = ((Finset.univ.image z : Finset X) : Set X).encard := by
          rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (zeroSetIn A b C).encard := Set.encard_le_encard hsub
end GlobalTheory.CompanionTheory.FSCrofton
