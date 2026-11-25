-- Prove2me | solution 1 for GlobalTheory.ArchMetric.slope_scaleNormExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:23.044567+00:00
-- url     : https://prove2.me/submissions/445ccb5f-d5a4-4acd-a736-0a6f1b7ff36e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_arDeg_scaleNormExp

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
variable {A B : Submodule (𝓞 K) V}
namespace GlobalTheory.ArchMetric
theorem _root_.solution (t : (K →+* ℂ) → ℝ) (hA : A.FG) (h0 : A ≠ ⊥) :
    (h.scaleNormExp t).slope A = h.slope A - (∑ σ : K →+* ℂ, t σ) / finrank ℚ K := by
  have : (finrank (𝓞 K) A : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (finrank_lattice_pos hA h0).ne'
  rw [slope, slope, degNorm, degNorm, h.arDeg_scaleNormExp t hA]
  field_simp
end GlobalTheory.ArchMetric
