-- Prove2me | solution 1 for GlobalTheory.ArchMetric.coe_le_muMin_sq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:28:56.952473+00:00
-- url     : https://prove2.me/submissions/fdc93961-dab5-42b8-a883-d7e3c5d023e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_coe_le_muMin_iff

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
theorem _root_.solution {c : ℝ} : (c : EReal) ≤ h.muMin_sq A ↔ ∀ W : Submodule K V,
    ¬ A ≤ W.restrictScalars (𝓞 K) → c ≤ 2 * h.quotSlope A (A ⊓ W.restrictScalars (𝓞 K)) := by
  have : (c : EReal) ≤ h.muMin_sq A ↔ ((c / 2 : ℝ) : EReal) ≤ h.muMin A := by
    rw [muMin_sq, EReal.coe_div]
    exact (EReal.div_le_iff_le_mul (by norm_num) (EReal.coe_ne_top 2)).symm
  rw [this, coe_le_muMin_iff]
  simp only [div_le_iff₀' (two_pos : (0 : ℝ) < 2)]
end GlobalTheory.ArchMetric
