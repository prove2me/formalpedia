-- Prove2me | solution 1 for OAI.CompactMellinBridge.dirichletTarget_of_compact_normFiber_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:23:51.394646+00:00
-- url     : https://prove2.me/submissions/699c5d8f-2e58-4555-9a6a-6e9dc6054e24

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Theorems.Thm_OAI_CompactMellinBridge_weighted_sum_zero_near_small_D
import Theorems.Thm_OAI_CompactMellinBridge_compact_weight_mellin_analytic
import Theorems.Thm_OAI_CompactMellinBridge_pair_zero_free_of_compact_weight_bound
import Theorems.Thm_OAI_CompactMellinBridge_pair_zero_free_of_compact_weight_bound_principal_left
import Theorems.Thm_OAI_CompactMellinBridge_pair_zero_free_of_compact_weight_bound_principal_right
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeChar_ne_one_of_one
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_baseChangeWeight_zero
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_baseChange_eq_pairInverseCoeff
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
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution
    (hTest : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        BaseChangeCompactTest χ ρ) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · let T := hTest q χ ρ h23 hρ
    have hσone : T.sigma < 1 := lt_trans T.sigma_lt hρ
    have hρone : ρ ≠ 1 := by
      intro hh
      subst ρ
      norm_num at hρ
    have hc := ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff χ
    have hz := ShortDraftHeckeBridge.normFiberCoeff_baseChangeWeight_zero χ
    have hzeroTest :
        (fun D : ℝ => T.F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) :=
      weighted_sum_zero_near_small_D
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ)) hz T.W T.F
        (fun y hy => T.support y (Or.inr hy)) T.sum_eq
    have hWanalytic : AnalyticOnNhd ℂ (mellin T.W)
        {s : ℂ | T.sigma < s.re} :=
      compact_weight_mellin_analytic T.W T.smooth T.support T.sigma
    by_cases hχ : χ = 1
    · have hψ : ShortDraftHeckeBridge.baseChangeChar χ ≠ 1 :=
        ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one χ hχ
      have hc' : ∀ n : ℕ, n ≠ 0 →
          ShortDraftHeckeBridge.normFiberCoeff
            (ShortDraftHeckeBridge.baseChangeWeight χ) n =
            ShortDraftHeckeBridge.pairInverseCoeff
              (1 : DirichletCharacter ℂ q)
              (ShortDraftHeckeBridge.baseChangeChar χ) n := by
        intro n hn
        simpa only [hχ] using hc n hn
      have hpair := pair_zero_free_of_compact_weight_bound_principal_left
        (q := q) (ShortDraftHeckeBridge.baseChangeChar χ) hψ
        (ShortDraftHeckeBridge.baseChangeWeight χ) hc' hz
        T.W T.F T.sum_eq T.term_integrable T.fubini
        T.sigma hσone T.locally_integrable hzeroTest T.power_bound
        hWanalytic ρ T.sigma_lt hρone T.mellin_nonzero
      simpa only [hχ] using hpair.1
    · by_cases hψ : ShortDraftHeckeBridge.baseChangeChar χ = 1
      · have hc' : ∀ n : ℕ, n ≠ 0 →
            ShortDraftHeckeBridge.normFiberCoeff
              (ShortDraftHeckeBridge.baseChangeWeight χ) n =
              ShortDraftHeckeBridge.pairInverseCoeff χ
                (1 : DirichletCharacter ℂ (q * 3)) n := by
          intro n hn
          simpa only [hψ] using hc n hn
        exact (pair_zero_free_of_compact_weight_bound_principal_right
          χ hχ (ShortDraftHeckeBridge.baseChangeWeight χ) hc' hz
          T.W T.F T.sum_eq T.term_integrable T.fubini
          T.sigma hσone T.locally_integrable hzeroTest T.power_bound
          hWanalytic ρ T.sigma_lt hρone T.mellin_nonzero).1
      · exact (pair_zero_free_of_compact_weight_bound
          χ (ShortDraftHeckeBridge.baseChangeChar χ) hχ hψ
          (ShortDraftHeckeBridge.baseChangeWeight χ) (fun n hn => hc n hn) hz
          T.W T.F T.sum_eq T.term_integrable T.fubini
          T.sigma hσone T.locally_integrable hzeroTest T.power_bound
          hWanalytic ρ T.sigma_lt T.mellin_nonzero).1
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal
end OAI.CompactMellinBridge
