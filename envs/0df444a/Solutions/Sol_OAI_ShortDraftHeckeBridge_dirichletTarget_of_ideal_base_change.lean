-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.dirichletTarget_of_ideal_base_change
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:58:15.189287+00:00
-- url     : https://prove2.me/submissions/84257524-e484-4e7b-9333-8535c6d22761

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_baseChangeWeight_zero
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeChar_ne_one_of_one
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_zero_free_of_normFiber_exp_power_bound_only
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_zero_free_of_normFiber_exp_power_bound_principal_left
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_zero_free_of_normFiber_exp_power_bound_principal_right
import Theorems.Thm_OAI_ShortDraft_dirichlet_target_of_one_le_re
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    (hcoeff : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (n : ℕ), n ≠ 0 →
        normFiberCoeff (baseChangeWeight χ) n =
          pairInverseCoeff χ (baseChangeChar χ) n)
    (hbound : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        ∃ σ : ℝ, 0 < σ ∧ σ < ρ.re ∧
          (fun D : ℝ => normFiberExpSum (baseChangeWeight χ) D⁻¹) =O[atTop]
            (fun D : ℝ => D ^ σ)) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · obtain ⟨σ, hσpos, hσρ, htop⟩ := hbound q χ ρ h23 hρ
    have hσone : σ < 1 := lt_trans hσρ hρ
    have hρone : ρ ≠ 1 := by
      intro hh
      subst ρ
      norm_num at hρ
    have hc := hcoeff q χ
    have hz := normFiberCoeff_baseChangeWeight_zero χ
    by_cases hχ : χ = 1
    · have hψ : baseChangeChar χ ≠ 1 :=
        baseChangeChar_ne_one_of_one χ hχ
      have hc' : ∀ n : ℕ, n ≠ 0 →
          normFiberCoeff (baseChangeWeight χ) n =
            pairInverseCoeff (1 : DirichletCharacter ℂ q)
              (baseChangeChar χ) n := by
        intro n hn
        simpa only [hχ] using hc n hn
      have hpair := pair_zero_free_of_normFiber_exp_power_bound_principal_left
        (q := q) (baseChangeChar χ) hψ (baseChangeWeight χ)
        hc' hz σ hσpos hσone htop ρ hσρ hρone
      simpa only [hχ] using hpair.1
    · by_cases hψ : baseChangeChar χ = 1
      · have hc' : ∀ n : ℕ, n ≠ 0 →
            normFiberCoeff (baseChangeWeight χ) n =
              pairInverseCoeff χ (1 : DirichletCharacter ℂ (q * 3)) n := by
          intro n hn
          simpa only [hψ] using hc n hn
        exact (pair_zero_free_of_normFiber_exp_power_bound_principal_right
          χ hχ (baseChangeWeight χ) hc' hz σ hσpos hσone htop ρ hσρ hρone).1
      · exact (pair_zero_free_of_normFiber_exp_power_bound_only
          χ (baseChangeChar χ) hχ hψ (baseChangeWeight χ)
          (fun n hn => hc n hn) hz σ hσpos hσone htop ρ hσρ).1
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal
end OAI.ShortDraftHeckeBridge
