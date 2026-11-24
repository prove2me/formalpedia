-- Prove2me | solution 1 for GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:40:42.519149+00:00
-- url     : https://prove2.me/submissions/0279340a-cfd0-4002-bee1-8463dfaa5ac3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Theorems.Thm_GlobalTheory_UnitLemma_isIntegral_of_isLat_stable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma
open Polynomial in
private lemma latticeCount_eq_zero_of_not_isIntegral_lemma (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (hB : ¬ IsIntegral K.O B.g) (k : B.Cl) :
    B.N k.rep = 0 := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum _root_.GlobalTheory.UnitLemma.InvAlg.X
  refine finsum_eq_zero_of_forall_eq_zero fun o => absurd ?_ hB
  obtain ⟨hfull, hstab, -⟩ := (Quot.out o).2
  exact _root_.GlobalTheory.UnitLemma.isIntegral_of_isLat_stable _ hfull _ hstab
open Polynomial in
private lemma stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (hB : ¬ IsIntegral K.O B.g) :
    B.stSum = 0 := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.stSum
  exact finsum_eq_zero_of_forall_eq_zero fun k => latticeCount_eq_zero_of_not_isIntegral_lemma K B hB k
end GlobalTheory.UnitLemma
end

set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
namespace GlobalTheory.UnitLemma
namespace _root_.GlobalTheory.UnitLemma
theorem _root_.solution :
    ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B₁ B₂ : _root_.GlobalTheory.UnitLemma.InvAlg K),
      ¬ (IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g) →
      _root_.GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ = 0 ∧
        B₁.stSum * B₂.stSum = 0 := by
  intro K B₁ B₂ h
  have hprod : ¬ IsIntegral K.O (B₁.prod B₂).g := by
    intro hi
    have hi' : IsIntegral K.O ((B₁.g, B₂.g) : B₁.A × B₂.A) := hi
    apply h
    exact ⟨hi'.map (AlgHom.fst K.O B₁.A B₂.A), hi'.map (AlgHom.snd K.O B₁.A B₂.A)⟩
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.InvAlg.kapSum
    refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
    rw [latticeCount_eq_zero_of_not_isIntegral_lemma K _ hprod k, mul_zero]
  · by_cases h₁ : IsIntegral K.O B₁.g
    · rw [stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 K B₂ fun h₂ => h ⟨h₁, h₂⟩, mul_zero]
    · rw [stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 K B₁ h₁, zero_mul]
end _root_.GlobalTheory.UnitLemma
end GlobalTheory.UnitLemma
