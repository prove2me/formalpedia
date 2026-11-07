-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.pair_zero_free_of_normFiber_continuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:47:04.966787+00:00
-- url     : https://prove2.me/submissions/a6166c31-c33d-402b-b984-e2240d74cbc1

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiber_LSeries_eq_pair_inverse
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_inverse_euler_identity
import Theorems.Thm_OAI_ShortDraft_zero_free_of_analytic_identity


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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (σ : ℝ) (hσ : σ < 1) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hMseries : ∀ s : ℂ, 1 < s.re → M s = LSeries (normFiberCoeff weight) s)
    (ρ : ℂ) (hρ : σ < ρ.re) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (ψ.differentiable_LFunction hψ).differentiableOn
  have hL : AnalyticOnNhd ℂ (fun s => χ.LFunction s * ψ.LFunction s) U :=
    hLχ.mul hLψ
  have hW : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) U := analyticOnNhd_const
  have heq : ∀ s : ℂ, 1 < s.re →
      (χ.LFunction s * ψ.LFunction s) * M s = 1 := by
    intro s hs
    rw [hMseries s hs, normFiber_LSeries_eq_pair_inverse χ ψ weight hcoeff s]
    exact pair_inverse_euler_identity χ ψ s hs
  have hprod : χ.LFunction ρ * ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_analytic_identity σ hσ
      (fun s => χ.LFunction s * ψ.LFunction s) M (fun _ => (1 : ℂ))
      hL hM hW heq ρ hρ one_ne_zero
  exact mul_ne_zero_iff.mp hprod
end OAI.ShortDraftHeckeBridge
