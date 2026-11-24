-- Prove2me | solution 1 for GlobalTheory.PlaneTheta.atTop_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:27:13.513271+00:00
-- url     : https://prove2.me/submissions/2357ecac-8464-407d-b86b-3d60cfdc53d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics
import Theorems.Thm_GlobalTheory_PlaneTheta_exists_pos_le_of_summable
import Theorems.Thm_GlobalTheory_PlaneTheta_abs_tsum_le
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_add_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open scoped RealInnerProductSpace
open GlobalTheory GlobalTheory.PlaneTheta
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L]
namespace GlobalTheory.PlaneTheta
theorem _root_.solution (u : E) (hu : ∀ x : L, (x : E) + u ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' x : L, Real.exp (-Real.pi * t * ‖(x : E) + u‖ ^ 2))
      =O[atTop] (fun t => Real.exp (-c * t)) := by
  have h : Summable fun x : L => Real.exp (-(Real.pi * ‖(x : E) + u‖ ^ 2)) := by
    simpa only [neg_mul] using summable_lattice_exp_neg_mul_norm_add_sq L Real.pi_pos u
  obtain ⟨δ, hδ, hq⟩ := exists_pos_le_of_summable h
  refine ⟨δ, hδ, IsBigO.of_bound (Real.exp δ * ∑' x : L, Real.exp (-(Real.pi * ‖(x : E) + u‖ ^ 2))) ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  refine abs_tsum_le ht h (fun x => ?_) (fun x _ => hq x ?_)
  · rw [abs_of_pos (Real.exp_pos _)]
    apply le_of_eq; congr 1; ring
  · have := norm_pos_iff.2 (hu x)
    have := Real.pi_pos
    positivity
end GlobalTheory.PlaneTheta
