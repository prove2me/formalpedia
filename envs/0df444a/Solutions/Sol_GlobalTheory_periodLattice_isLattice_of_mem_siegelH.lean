-- Prove2me | solution 1 for GlobalTheory.periodLattice_isLattice_of_mem_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:49:42.57843+00:00
-- url     : https://prove2.me/submissions/c54d0245-f175-4bb6-8e3f-ea9cea33f487

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Theorems.Thm_GlobalTheory_isUnit_det_im_of_mem_siegelH
import Theorems.Thm_GlobalTheory_discreteTopology_periodLattice_of_isUnit
import Theorems.Thm_GlobalTheory_span_periodLattice_eq_top_of_isUnit
import Theorems.Thm_GlobalTheory_intVec_eq_zero_of_period_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
      DiscreteTopology (periodLattice τ) ∧
      Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧
      ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0 := by
  intro g τ hτ
  have h := isUnit_det_im_of_mem_siegelH hτ
  exact ⟨discreteTopology_periodLattice_of_isUnit h, span_periodLattice_eq_top_of_isUnit h,
    intVec_eq_zero_of_period_eq_zero h⟩
end GlobalTheory
