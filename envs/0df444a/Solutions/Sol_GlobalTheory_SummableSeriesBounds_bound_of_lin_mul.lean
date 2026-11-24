-- Prove2me | solution 1 for GlobalTheory.SummableSeriesBounds.bound_of_lin_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:46.963333+00:00
-- url     : https://prove2.me/submissions/39ebb4ab-36fd-467e-9226-b57c0ad8994f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_coeff_succ_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
namespace GlobalTheory.SummableSeriesBounds
theorem _root_.solution {π : C} (hπ : ‖π‖ < 1) {G : PowerSeries C} {b c : ℝ}
    (hc : ∀ n, ‖coeff n G‖ ≤ c) (hb : ∀ n, ‖coeff n ((X - PowerSeries.C π) * G)‖ ≤ b) (m : ℕ) :
    ‖coeff m G‖ ≤ b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  have key : ∀ k m, ‖coeff m G‖ ≤ max b (‖π‖ ^ k * c) := by
    intro k
    induction k with
    | zero => intro m; simpa using Or.inr (hc m)
    | succ k ih =>
      intro m
      have e : coeff m G = coeff (m + 1) ((X - PowerSeries.C π) * G) + π * coeff (m + 1) G := by
        rw [coeff_succ_lin]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hb _).trans (le_max_left _ _)) ?_)
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_left (ih (m + 1)) (norm_nonneg _)).trans ?_
      rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
      refine max_le_max (mul_le_of_le_one_left hb0 hπ.le) (le_of_eq (by ring))
  have ht : Tendsto (fun k : ℕ => max b (‖π‖ ^ k * c)) atTop (𝓝 (max b (0 * c))) :=
    tendsto_const_nhds.max ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ).mul_const c)
  rw [zero_mul, max_eq_left hb0] at ht
  exact ge_of_tendsto' ht fun k => key k m
end GlobalTheory.SummableSeriesBounds
