-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isOpen_setOf_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:55.298506+00:00
-- url     : https://prove2.me/submissions/2d9703ad-6456-4189-9504-cb86054a4fce

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_mul_mul_eq_one_of_rank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {K : Type*} [Field K] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m]
variable [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (k : ℕ) : IsOpen {A : Matrix m l K | k ≤ A.rank} := by
  classical
  rw [isOpen_iff_forall_mem_open]
  intro A₀ hA₀
  obtain ⟨L, R, hLR⟩ := exists_mul_mul_eq_one_of_rank A₀
  refine ⟨{A | (L * A * R).det ≠ 0}, fun A hA => ?_, ?_, ?_⟩
  · have hu : IsUnit (L * A * R) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hA)
    have h1 : (L * A * R).rank = A₀.rank := by
      rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
    have h2 : (L * A * R).rank ≤ A.rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    exact le_trans hA₀ (h1 ▸ h2)
  · have hc : Continuous fun A : Matrix m l K => (L * A * R).det :=
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
    exact isOpen_compl_singleton.preimage hc
  · show (L * A₀ * R).det ≠ 0
    rw [hLR, Matrix.det_one]
    exact one_ne_zero
end GroundTheory.Automorphic.Parabolic
