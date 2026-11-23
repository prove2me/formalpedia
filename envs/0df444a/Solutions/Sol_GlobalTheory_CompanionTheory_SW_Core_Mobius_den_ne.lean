-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Mobius.den_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:48.267728+00:00
-- url     : https://prove2.me/submissions/7426083b-6fd2-4cdb-be39-378397bbf8ee

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
    (c : ℂ) * τ + d ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  rcases him with hc | hτ
  · subst hc
    have hd : d = 0 := by simpa using hre
    subst hd
    simp at hdet
  · exact h.ne' hτ
end GlobalTheory.CompanionTheory.SW.Core.Mobius
