-- Prove2me | solution 1 for GlobalTheory.exists_variableChange_eq_latticeCurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:00.181221+00:00
-- url     : https://prove2.me/submissions/aabdeb2c-eb81-42c8-bb0a-b532e33a7918

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Theorems.Thm_GlobalTheory_mem_lattice_periodPairOfTau
import Theorems.Thm_GlobalTheory_latticeCurve_j
import Theorems.Thm_P2M_GlobalTheory_exists_E__cube_div_discriminant_eq_bed7c5b84d7f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups Filter EisensteinSeries
open scoped Real Topology
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • W = latticeCurve L := by
  obtain ⟨τ, hτ⟩ := exists_E₄_cube_div_discriminant_eq W.j
  refine ⟨periodPairOfTau τ, W.exists_variableChange_of_j_eq _ ?_⟩
  rw [latticeCurve_j one_ne_zero (mem_lattice_periodPairOfTau τ), hτ]
end GlobalTheory
