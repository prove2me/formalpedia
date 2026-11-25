-- Prove2me | solution 1 for GlobalTheory.ArchMetric.scale_gramDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:10:52.683679+00:00
-- url     : https://prove2.me/submissions/fcd0e5c4-06f6-4ee3-b2fb-67f7cb0d548b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_scale_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] {V V' V'' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [AddCommGroup V''] [Module K V'']
variable (h : ArchMetric K V)
variable (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) (σ : K →+* ℂ)
namespace GlobalTheory.ArchMetric
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → V) :
    (h.scale c hc).gramDet σ e = c σ ^ Fintype.card ι * h.gramDet σ e := by
  rw [gramDet, scale_gram, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, gramDet]
end GlobalTheory.ArchMetric
