-- Prove2me | solution 1 for GlobalTheory.ArchMetric.muMin_of_finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:37.234853+00:00
-- url     : https://prove2.me/submissions/1b99b381-6f05-4362-b238-033e1ac85f7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_finrank_inf_restrictScalars_lt
import Theorems.Thm_GlobalTheory_ArchMetric_coe_le_muMin_iff
import Theorems.Thm_GlobalTheory_ArchMetric_muMin_le_slope

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
theorem _root_.solution (hA : A.FG) (h1 : finrank (𝓞 K) A = 1) :
    h.muMin A = h.slope A := by
  have h0 : A ≠ ⊥ := by
    rintro rfl
    simp at h1
  refine le_antisymm (h.muMin_le_slope h0) (h.coe_le_muMin_iff.2 fun W hW => ?_)
  have : A ⊓ W.restrictScalars (𝓞 K) = ⊥ := by
    by_contra hne
    have h2 := finrank_lattice_pos (hA.of_le inf_le_left) hne
    have h3 := finrank_inf_restrictScalars_lt hA hW
    omega
  rw [this, quotSlope_bot]
end GlobalTheory.ArchMetric
