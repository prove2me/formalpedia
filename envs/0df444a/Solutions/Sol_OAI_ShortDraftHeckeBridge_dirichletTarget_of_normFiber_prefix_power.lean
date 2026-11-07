-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.dirichletTarget_of_normFiber_prefix_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:25:02.078879+00:00
-- url     : https://prove2.me/submissions/173f273e-c39d-4d54-909a-9969c4389646

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_ShortDraftHeckeBridge_dirichletTarget_of_normFiber_exp_bound
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_baseChangeWeight_zero
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_baseChange_eq_pairInverseCoeff
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberExpSum_isBigO_of_prefix_power


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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    (hprefix : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        ∃ σ C : ℝ, 0 < σ ∧ σ < ρ.re ∧ σ ≤ 1 ∧ 0 ≤ C ∧
          ∀ n : ℕ,
            ‖prefixCoeff (normFiberCoeff (baseChangeWeight χ)) n‖ ≤
              C * (((n : ℝ) + 1) ^ σ)) :
    ShortDraft.DirichletTarget := by
  apply dirichletTarget_of_normFiber_exp_bound
  intro q _ χ ρ h23 hρ
  obtain ⟨σ, C, hσpos, hσρ, hσone, hC, hsum⟩ :=
    hprefix q χ ρ h23 hρ
  refine ⟨σ, hσpos, hσρ, ?_⟩
  apply normFiberExpSum_isBigO_of_prefix_power χ (baseChangeChar χ)
    (baseChangeWeight χ)
    (normFiberCoeff_baseChange_eq_pairInverseCoeff χ)
    (normFiberCoeff_baseChangeWeight_zero χ)
    σ C hσpos.le hσone hC hsum
end OAI.ShortDraftHeckeBridge
