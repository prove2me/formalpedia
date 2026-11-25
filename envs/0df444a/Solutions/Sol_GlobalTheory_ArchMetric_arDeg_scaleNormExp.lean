-- Prove2me | solution 1 for GlobalTheory.ArchMetric.arDeg_scaleNormExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:02:27.471135+00:00
-- url     : https://prove2.me/submissions/2bea3854-72f4-4097-8f22-723491731144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_arDeg_scale

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
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A : Submodule (𝓞 K) V} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchMetric
theorem _root_.solution (t : (K →+* ℂ) → ℝ) (hA : A.FG) :
    (h.scaleNormExp t).arDeg A = h.arDeg A - finrank (𝓞 K) A * ∑ σ : K →+* ℂ, t σ := by
  rw [scaleNormExp, arDeg_scale _ _ _ hA]
  simp only [Real.log_exp, ← Finset.mul_sum]
  ring
end GlobalTheory.ArchMetric
