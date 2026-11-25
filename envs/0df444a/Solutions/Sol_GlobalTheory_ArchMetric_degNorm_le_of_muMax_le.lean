-- Prove2me | solution 1 for GlobalTheory.ArchMetric.degNorm_le_of_muMax_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:34.41508+00:00
-- url     : https://prove2.me/submissions/a31350ce-f652-420d-a7aa-1f6949ecb41f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_finrank_mul_slope

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
theorem _root_.solution (hA : A.FG) (hBA : B ≤ A) {c : ℝ} (hc : h.muMax A ≤ c) :
    h.degNorm B ≤ finrank (𝓞 K) B * c := by
  by_cases h0 : B = ⊥
  · subst h0
    simp
  · rw [← h.finrank_mul_slope (hA.of_le hBA) h0]
    exact mul_le_mul_of_nonneg_left (h.muMax_le_coe_iff.1 hc B hBA h0) (Nat.cast_nonneg _)
end GlobalTheory.ArchMetric
