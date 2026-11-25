-- Prove2me | solution 1 for GlobalTheory.ArchMetric.norm_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:26:39.718519+00:00
-- url     : https://prove2.me/submissions/10991372-a9ff-41c0-9c06-c488002327a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice

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
namespace GlobalTheory.ArchMetric
theorem _root_.solution (σ : K →+* ℂ) (x y : V) :
    h.norm σ (x + y) ^ 2 = h.norm σ x ^ 2 + 2 * (h.form σ x y).re + h.norm σ y ^ 2 := by
  have : (h.form σ y x).re = (h.form σ x y).re := by rw [h.form_symm σ x y, Complex.conj_re]
  simp only [norm_sq, map_add, LinearMap.add_apply, Complex.add_re, this]
  ring
end GlobalTheory.ArchMetric
