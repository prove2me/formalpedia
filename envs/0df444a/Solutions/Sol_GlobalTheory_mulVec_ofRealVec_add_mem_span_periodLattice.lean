-- Prove2me | solution 1 for GlobalTheory.mulVec_ofRealVec_add_mem_span_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:29.623103+00:00
-- url     : https://prove2.me/submissions/e1e43aca-a08b-4690-96a9-cef011ba2cc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice

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
omit [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (τ : Matrix ι ι ℂ) (u v : ι → ℝ) :
    τ *ᵥ ofRealVec u + ofRealVec v ∈
      Submodule.span ℝ (periodLattice τ : Set (ι → ℂ)) := by
  classical
  have e : ∀ u : ι → ℝ, ofRealVec u = ∑ j, u j • ofIntVec (Pi.single j (1 : ℤ)) := by
    intro u
    ext i
    simp [ofRealVec, ofIntVec, Finset.sum_apply, Pi.single_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [e u, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single j 1, 0, ?_⟩)
    rw [ofIntVec_zero, add_zero]
  · rw [e v]
    refine Submodule.sum_mem _ fun j _ => ?_
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, Pi.single j 1, ?_⟩)
    rw [ofIntVec_zero, Matrix.mulVec_zero, zero_add]
end GlobalTheory
