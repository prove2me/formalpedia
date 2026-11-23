-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Mobius.im_frac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:48.43746+00:00
-- url     : https://prove2.me/submissions/aff5ee65-786e-47c3-832d-f96a6fdb67ff

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MobiusActionUpperHalfPlane

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Mobius
namespace GlobalTheory.CompanionTheory.SW.Core.Mobius
theorem _root_.solution (a b c d : ℝ) (hdet : a * d - b * c = 1) (τ : ℂ) (h : 0 < τ.im) :
    (((a : ℂ) * τ + b) / ((c : ℂ) * τ + d)).im = τ.im / ‖(c : ℂ) * τ + d‖ ^ 2 := by
  rw [Complex.div_im, ← Complex.normSq_eq_norm_sq, ← sub_div]
  congr 1
  simp
  linear_combination τ.im * hdet
end GlobalTheory.CompanionTheory.SW.Core.Mobius
