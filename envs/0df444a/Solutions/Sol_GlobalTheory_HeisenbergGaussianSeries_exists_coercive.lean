-- Prove2me | solution 1 for GlobalTheory.HeisenbergGaussianSeries.exists_coercive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:09.77737+00:00
-- url     : https://prove2.me/submissions/c2dc6dc7-d451-4129-a6cb-2cc8baa54ee1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup
import Theorems.Thm_GlobalTheory_IntegralPointNormSquareBound_exists_pos_mul_norm_sq_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.HeisenbergGaussianSeries
namespace GlobalTheory.HeisenbergGaussianSeries
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (hpos : ∀ v, v ≠ 0 → 0 < om v (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ om v (J v) := by
  first
  | exact @_root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le
  | exact _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le
  | (apply _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le ..)
end GlobalTheory.HeisenbergGaussianSeries
