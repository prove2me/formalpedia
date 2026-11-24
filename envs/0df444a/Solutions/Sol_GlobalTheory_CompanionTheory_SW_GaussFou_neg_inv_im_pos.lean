-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussFou.neg_inv_im_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:18:51.206413+00:00
-- url     : https://prove2.me/submissions/a95d5d37-46fc-428e-a8c4-1ba833f73db5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransformStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GaussFou
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.GaussFou
theorem _root_.solution {τ : ℂ} (h : 0 < τ.im) : 0 < (-τ⁻¹).im := by
  have hne : τ ≠ 0 := fun h0 => by simp [h0] at h
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos h (Complex.normSq_pos.2 hne)
end GlobalTheory.CompanionTheory.SW.GaussFou
