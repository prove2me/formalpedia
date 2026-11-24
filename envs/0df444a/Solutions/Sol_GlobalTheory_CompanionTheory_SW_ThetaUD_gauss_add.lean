-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThetaUD.gauss_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:04.733215+00:00
-- url     : https://prove2.me/submissions/ee92ed3c-22a1-4d28-b964-d9cab3732b99

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThetaUD
variable {F : Type} [Field F] [NumberField F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.ThetaUD
theorem _root_.solution (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (c : InfinitePlace F → ℝ) (y : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => τ w + (c w : ℝ)) y = gauss B ρ P τ y *
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        ∑ w, ((c w : ℂ) * ((y w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))) := by
  unfold gauss
  rw [← Complex.exp_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
  push_cast
  ring
end GlobalTheory.CompanionTheory.SW.ThetaUD
