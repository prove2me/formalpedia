-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothParam.contDiff_weight_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:46.08619+00:00
-- url     : https://prove2.me/submissions/1e3f2856-3536-49fd-9054-f5ef2da0374d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_contDiff_pderiv
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_hasFDerivAt_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothParam
variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory.CompanionTheory.SmoothParam
theorem _root_.solution {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (H : P × Y → F),
      ContDiff ℝ ∞ H → ContDiff ℝ n (fun p => ∫ x, u x • H (p, ψ x) ∂ν) := by
  induction n with
  | zero =>
    intro F _ _ _ H hH
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun p =>
      (hasFDerivAt_weight hu hψ hK hψK hH p).continuousAt
  | succ n ih =>
    intro F _ _ _ H hH
    have hfd : fderiv ℝ (fun p => ∫ x, u x • H (p, ψ x) ∂ν)
        = fun p => ∫ x, u x • pderiv H (p, ψ x) ∂ν := by
      funext p
      exact (hasFDerivAt_weight hu hψ hK hψK hH p).fderiv
    have : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [this, contDiff_succ_iff_fderiv]
    refine ⟨fun p => (hasFDerivAt_weight hu hψ hK hψK hH p).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih (P →L[ℝ] F) (pderiv H) (contDiff_pderiv hH)
end GlobalTheory.CompanionTheory.SmoothParam
