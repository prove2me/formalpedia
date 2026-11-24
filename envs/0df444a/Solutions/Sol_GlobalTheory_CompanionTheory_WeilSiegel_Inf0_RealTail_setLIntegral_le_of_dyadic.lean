-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.setLIntegral_le_of_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:15:44.988769+00:00
-- url     : https://prove2.me/submissions/a53475e2-f851-46b1-bc5a-f508c87ea032

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_measurableSet_boxR
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_exists_dyadic_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
variable {P ι : Type} [Fintype P] [Fintype ι]
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
theorem _root_.solution (f : (P → ι → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (M : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (T : Set (P → ι → ℝ)) (hT : MeasurableSet T)
    (hTK : ∀ x ∈ T, f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) ≤ K) (B : ℝ≥0∞)
    (hB : ∀ j : ℕ, volume (T ∩ boxR (fun _ => (2 : ℝ) ^ j)) ≤
      B * ENNReal.ofReal (((2 : ℝ) ^ j) ^ M)) :
    ∫⁻ x in T, ENNReal.ofReal (f x) ≤ ENNReal.ofReal (2 * K * 2 ^ (M + 1)) * B := by
  let c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (K * 2 ^ (M + 1) * (1 / 2) ^ (j * (M + 1)))
  have h1 : ∫⁻ x in T, ENNReal.ofReal (f x) ≤ ∫⁻ x in T, ∑' j,
      (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)).indicator (fun _ => c j) x := by
    refine setLIntegral_mono' hT fun x hx => ?_
    obtain ⟨j, hj, hfj⟩ := exists_dyadic_bound f (M + 1) K x (hf x) (hTK x hx)
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem hj]
    exact ENNReal.ofReal_le_ofReal hfj
  refine h1.trans ?_
  rw [lintegral_tsum (fun j => (measurable_const.indicator (measurableSet_boxR _)).aemeasurable)]
  have h2 : ∀ j : ℕ, ∫⁻ x in T,
      (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)).indicator (fun _ => c j) x ≤
      ENNReal.ofReal (K * 2 ^ (M + 1)) * B * ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
    intro j
    rw [lintegral_indicator_const (measurableSet_boxR _),
      Measure.restrict_apply (measurableSet_boxR _), Set.inter_comm]
    have e : ((1 : ℝ) / 2) ^ (j * (M + 1)) * ((2 : ℝ) ^ j) ^ M = (1 / 2) ^ j := by
      have : ((1 : ℝ) / 2) ^ (j * (M + 1)) = (1 / 2) ^ j * ((1 / 2) ^ j) ^ M := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      rw [this, mul_assoc, ← mul_pow, ← mul_pow]; norm_num
    calc c j * volume (T ∩ boxR (fun _ => (2 : ℝ) ^ j))
        ≤ c j * (B * ENNReal.ofReal (((2 : ℝ) ^ j) ^ M)) := by gcongr; exact hB j
      _ = ENNReal.ofReal (K * 2 ^ (M + 1)) * B *
            (ENNReal.ofReal ((1 / 2) ^ (j * (M + 1))) * ENNReal.ofReal (((2 : ℝ) ^ j) ^ M)) := by
          simp only [c]
          rw [ENNReal.ofReal_mul (by positivity)]
          ring
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), e]
  refine (ENNReal.tsum_le_tsum h2).trans ?_
  rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    summable_geometric_two, tsum_geometric_two]
  have e : (2 * K * 2 ^ (M + 1) : ℝ) = K * 2 ^ (M + 1) * 2 := by ring
  rw [e, ENNReal.ofReal_mul (p := K * 2 ^ (M + 1)) (q := 2) (by positivity)]
  apply le_of_eq
  ring
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
