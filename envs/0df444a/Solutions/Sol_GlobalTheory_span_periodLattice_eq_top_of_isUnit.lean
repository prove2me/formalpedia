-- Prove2me | solution 1 for GlobalTheory.span_periodLattice_eq_top_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:51.474573+00:00
-- url     : https://prove2.me/submissions/db489430-31fe-42e9-9b10-fc0235b9fabc

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Theorems.Thm_GlobalTheory_mulVec_periodCoordFst_add_periodCoordSnd
import Theorems.Thm_GlobalTheory_mulVec_ofRealVec_add_mem_span_periodLattice

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
theorem _root_.solution {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) :
    Submodule.span ℝ (periodLattice τ : Set (ι → ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  rw [← mulVec_periodCoordFst_add_periodCoordSnd hτ w]
  exact mulVec_ofRealVec_add_mem_span_periodLattice τ _ _
end GlobalTheory
