-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.nnnorm_changeOrigin_le_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:26.071602+00:00
-- url     : https://prove2.me/submissions/39b78165-ec64-4e42-a3a7-5bab3bfe9bf1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_AnalyticHypoSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open scoped ContDiff NNReal ENNReal Topology
open Set Filter
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (p : FormalMultilinearSeries ℝ E F) {ρ K : ℝ≥0}
    (hρ : 0 < ρ) (hK : ∀ n, ‖p n‖₊ ≤ K / ρ ^ n) {z : E} (hz : 4 * ‖z‖₊ ≤ ρ)
    (hzr : (‖z‖₊ : ℝ≥0∞) < p.radius) (k : ℕ) :
    ‖p.changeOrigin z k‖₊ ≤ 2 * (K * (2 / ρ) ^ k) := by
  have hsum := p.changeOriginSeries_summable_aux₂ hzr k
  have h1 := p.nnnorm_changeOrigin_le k hzr
  rw [← ENNReal.coe_le_coe] at h1 ⊢
  refine h1.trans ?_
  rw [ENNReal.coe_tsum hsum, ENNReal.tsum_sigma']
  have hterm : ∀ l : ℕ, ∑' _b : { s : Finset (Fin (k + l)) // s.card = l },
      ((‖p (k + l)‖₊ * ‖z‖₊ ^ l : ℝ≥0) : ℝ≥0∞)
      ≤ ((K * (2 / ρ) ^ k * (2⁻¹) ^ l : ℝ≥0) : ℝ≥0∞) := by
    intro l
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len,
      Fintype.card_fin, nsmul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    have hK' := hK (k + l)
    rw [← NNReal.coe_le_coe] at hK'
    push_cast at hK' ⊢
    have hz' : 4 * ‖z‖ ≤ (ρ : ℝ) := by exact_mod_cast hz
    have hch : ((k + l).choose l : ℝ) ≤ 2 ^ (k + l) := by
      exact_mod_cast Nat.choose_le_two_pow _ _
    have hρ' : (0 : ℝ) < ρ := hρ
    calc ((k + l).choose l : ℝ) * (‖p (k + l)‖ * ‖z‖ ^ l)
        ≤ 2 ^ (k + l) * ((K : ℝ) / (ρ : ℝ) ^ (k + l) * ((ρ : ℝ) / 4) ^ l) := by
          gcongr
          linarith
      _ = (K : ℝ) * (2 / (ρ : ℝ)) ^ k * (2⁻¹) ^ l := by
          have h4 : (4 : ℝ) ^ l = 2 ^ l * 2 ^ l := by rw [← mul_pow]; norm_num
          rw [pow_add, pow_add, div_pow, div_pow, inv_pow, h4]
          field_simp
  refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
  simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv_two]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  push_cast
  ring
end GroundTheory.Automorphic.Sobolev
