-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThetaUD.gauss_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:05.430187+00:00
-- url     : https://prove2.me/submissions/c3f68654-d9d3-4517-874b-d36f5db08035

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
    gauss B ρ P (fun w => ((c w : ℝ) : ℂ) ^ 2 * τ w) y = gauss B ρ P τ (fun w => c w • y w) := by
  unfold gauss
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hre : (((c w : ℝ) : ℂ) ^ 2 * τ w).re = c w ^ 2 * (τ w).re := by
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have him : (((c w : ℝ) : ℂ) ^ 2 * τ w).im = c w ^ 2 * (τ w).im := by
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
  rw [hre, him]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  ring
end GlobalTheory.CompanionTheory.SW.ThetaUD
