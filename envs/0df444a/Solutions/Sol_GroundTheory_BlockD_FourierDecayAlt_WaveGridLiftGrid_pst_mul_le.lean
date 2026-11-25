-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pst_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:11:51.66729+00:00
-- url     : https://prove2.me/submissions/80c0d2c5-4b4f-4b0a-a8a0-3abae390e2e6

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_Bracket
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PstMul
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_bracket_const_le
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_bracket_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
open Finset
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
theorem _root_.solution (k r : ℕ) (lam u v : ℕ → ℝ) (e e' : ℕ) (c g b Y : ℝ) (hk : 2 ≤ k) (hc : 0 ≤ c)
    (hg : 1 + c ≤ g) (hb : 3 ≤ b) (hkb : (k : ℝ) ≤ b) (hcb : c + 2 ≤ b) (hY : |Y| ≤ b)
    (hlam : ∀ s, 1 ≤ s → s ≤ k + 2 * r + 1 → |lam s| ≤ b)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s)
    (hp : PairOK k lam u e (-Y)) (hp' : PairOK k lam v e' (-Y))
    (hden : ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + u i|) (hden' : ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + v i|) :
    Pst k r lam c Y * Pst k r lam c (Y + 1) ≤
      b ^ (8 * r + 20) * ∏ i ∈ Icc 1 k, (|Y + 1 / 2 + u i| * |Y + 1 / 2 + v i|) := by
  have hP1 := bracket_le k r lam u e c g b Y 0 hk hc hg (Or.inl rfl) (by linarith) hY hlam hgap hp hden
  have hP2 := bracket_le k r lam v e' c g b Y 1 hk hc hg (Or.inr rfl) (by linarith) hY hlam hgap hp' hden'
  simp only [add_zero] at hP1
  have hKc := bracket_const_le k r c b hc hb hkb hcb
  have hKc0 : 0 ≤ (2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (pow_nonneg (by linarith) _)
  have hPu : 0 ≤ ∏ i ∈ Icc 1 k, |Y + 1 / 2 + u i| := prod_nonneg fun _ _ => abs_nonneg _
  have hPv : 0 ≤ ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := prod_nonneg fun _ _ => abs_nonneg _
  have hQ : 0 ≤ ∏ s ∈ Icc 1 (k + 2 * r + 1), (|Y + 1 + lam s| + c) :=
    prod_nonneg fun _ _ => add_nonneg (abs_nonneg _) hc
  unfold Pst
  rw [prod_mul_distrib]
  calc (∏ s ∈ Icc 1 (k + 2 * r + 1), (|Y + lam s| + c)) *
        ∏ s ∈ Icc 1 (k + 2 * r + 1), (|Y + 1 + lam s| + c)
      ≤ ((2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + u i|) *
        ((2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) :=
        mul_le_mul hP1 hP2 hQ (mul_nonneg hKc0 hPu)
    _ = ((2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3)) *
          ((2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3)) *
          ((∏ i ∈ Icc 1 k, |Y + 1 / 2 + u i|) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) := by ring
    _ ≤ (b ^ (4 * r + 10) * b ^ (4 * r + 10)) *
          ((∏ i ∈ Icc 1 k, |Y + 1 / 2 + u i|) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hKc hKc hKc0 (hKc0.trans hKc)) (mul_nonneg hPu hPv)
    _ = b ^ (8 * r + 20) *
          ((∏ i ∈ Icc 1 k, |Y + 1 / 2 + u i|) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) := by ring
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
