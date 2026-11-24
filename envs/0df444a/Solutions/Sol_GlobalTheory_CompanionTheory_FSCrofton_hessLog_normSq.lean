-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.hessLog_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:29:59.005076+00:00
-- url     : https://prove2.me/submissions/48f35cff-bac7-46fd-b6a2-bd06a4310e41

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudy
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_of_differentiableAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_of_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton Filter Topology
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.FSCrofton
theorem _root_.solution {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (j c : Fin n) :
    wd n j (wdb n c (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n c g x) := by
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    (hg.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)
  have hgx : DifferentiableAt ℂ g x := hg.differentiableAt (by simp)
  have hf : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y; rw [Complex.mul_conj]
  have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
  have hh : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n c)) x :=
    (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  have hE : wdb n c (fun y => g y * conj (g y)) =ᶠ[𝓝 x]
      fun y => g y * conj (fderiv ℂ g y (bas n c)) := by
    filter_upwards [hgd] with y hy
    rw [wdb_mul (hy.restrictScalars ℝ) (differentiableAt_conj (hy.restrictScalars ℝ)),
      wdb_of_differentiableAt hy, wdb_conj (hy.restrictScalars ℝ), wd_of_differentiableAt hy]
    ring
  rw [hf, wd_congr hE, wd_mul (f := g) (g := fun y => conj (fderiv ℂ g y (bas n c)))
    (hgx.restrictScalars ℝ) (differentiableAt_conj (hh.restrictScalars ℝ)),
    wd_conj (hh.restrictScalars ℝ), wdb_of_differentiableAt hh]
  simp [wd_of_differentiableAt hgx]
end GlobalTheory.CompanionTheory.FSCrofton
