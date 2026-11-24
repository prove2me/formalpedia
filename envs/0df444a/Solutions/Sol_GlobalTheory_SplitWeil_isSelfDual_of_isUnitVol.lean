-- Prove2me | solution 1 for GlobalTheory.SplitWeil.isSelfDual_of_isUnitVol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:23:30.008809+00:00
-- url     : https://prove2.me/submissions/87e70f25-ba08-4232-b672-3b6045ba08d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_fourier_inversion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
omit [ν.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (h : HasConductor ψ 1) (hν : IsUnitVol ν) : IsSelfDual ψ ν := by
  haveI := hν.1
  refine ⟨hν.1, fun f hf => ?_⟩
  rw [fourier_inversion ν h hf, Measure.real, hν.2, nabs_one]
  simp
end GlobalTheory.SplitWeil
