-- Prove2me | solution 1 for GlobalTheory.ArchMetric.muMax_sq_le_coe_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:09:51.054518+00:00
-- url     : https://prove2.me/submissions/8fb41923-5c7d-42e1-bbe8-bff590ee4998

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_slope_sq_eq

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
theorem _root_.solution {c : ℝ} :
    h.muMax_sq A ≤ c ↔ ∀ B ≤ A, B ≠ ⊥ → h.slope_sq B ≤ c := by
  have : h.muMax_sq A ≤ c ↔ h.muMax A ≤ ((c / 2 : ℝ) : EReal) := by
    rw [muMax_sq, EReal.coe_div, mul_comm]
    exact (EReal.le_div_iff_mul_le (by norm_num) (EReal.coe_ne_top 2)).symm
  rw [this, muMax_le_coe_iff]
  simp only [slope_sq_eq, le_div_iff₀' (two_pos : (0 : ℝ) < 2)]
end GlobalTheory.ArchMetric
