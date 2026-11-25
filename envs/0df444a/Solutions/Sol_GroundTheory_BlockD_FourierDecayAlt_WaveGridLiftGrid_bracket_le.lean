-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.bracket_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:04:01.673805+00:00
-- url     : https://prove2.me/submissions/46d4f68f-49d7-4a20-9fd1-03a934f38fd0

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_CloudProd
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_CloudPair
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_Bracket
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_pair_le
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_prod_le


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
theorem _root_.solution (k r : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (c g b Y ε : ℝ) (hk : 2 ≤ k) (hc : 0 ≤ c) (hg : 1 + c ≤ g)
    (hε : ε = 0 ∨ ε = 1) (hcb : c + 1 ≤ b) (hY : |Y| ≤ b)
    (hlam : ∀ s, 1 ≤ s → s ≤ k + 2 * r + 1 → |lam s| ≤ b)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s)
    (hp : PairOK k lam v e (-Y)) (hden : ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + v i|) :
    ∏ s ∈ Icc 1 (k + 2 * r + 1), (|Y + ε + lam s| + c) ≤
      (2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
  have hsplit : Icc 1 (k + 2 * r + 1) = Icc 1 (k - 1) ∪ Icc k (k + 2 * r + 1) := by
    ext s
    simp only [mem_union, mem_Icc]
    omega
  have hdisj : Disjoint (Icc 1 (k - 1)) (Icc k (k + 2 * r + 1)) := by
    rw [disjoint_left]
    intro s hs ht
    rw [mem_Icc] at hs ht
    omega
  have hε0 : |ε| ≤ 1 := by rcases hε with h0 | h0 <;> simp [h0]
  have hb : 0 ≤ b := le_trans (abs_nonneg Y) hY

  have hnode : ∏ s ∈ Icc k (k + 2 * r + 1), (|Y + ε + lam s| + c) ≤ (3 * b) ^ (2 * r + 2) := by
    have hcard : (Icc k (k + 2 * r + 1)).card = 2 * r + 2 := by
      rw [Nat.card_Icc]
      omega
    rw [← hcard, ← prod_const]
    refine prod_le_prod (fun s _ => by positivity) fun s hs => ?_
    rw [mem_Icc] at hs
    have h1 := abs_add_le (Y + ε) (lam s)
    have h2 := abs_add_le Y ε
    have h3 := hlam s (by omega) hs.2
    linarith

  have hpair := cloud_pair_le k lam v e c g b Y ε hk hc hg hε hcb hY
    (fun s hs1 hs2 => hlam s hs1 (by omega)) hgap hp hden
  have hcloud := cloud_prod_le k lam c g Y (by omega) hc hg hgap
  have hDn : 0 ≤ ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := prod_nonneg fun i _ => abs_nonneg _
  have hb3 : 0 ≤ 3 * b := by linarith
  have hcl : ∏ s ∈ Icc 1 (k - 1), (|Y + ε + lam s| + c) ≤
      3 * b * ((2 + c) ^ 2 * (k : ℝ) ^ 2) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
    refine le_trans hpair ?_
    apply mul_le_mul_of_nonneg_right _ hDn
    exact mul_le_mul_of_nonneg_left hcloud hb3
  have hcl0 : 0 ≤ ∏ s ∈ Icc 1 (k - 1), (|Y + ε + lam s| + c) :=
    prod_nonneg fun s _ => by positivity
  have hnode0 : 0 ≤ (3 * b) ^ (2 * r + 2) := pow_nonneg hb3 _
  rw [hsplit, prod_union hdisj]
  calc (∏ s ∈ Icc 1 (k - 1), (|Y + ε + lam s| + c)) *
        ∏ s ∈ Icc k (k + 2 * r + 1), (|Y + ε + lam s| + c)
      ≤ (3 * b * ((2 + c) ^ 2 * (k : ℝ) ^ 2) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) *
        (3 * b) ^ (2 * r + 2) := mul_le_mul hcl hnode (prod_nonneg fun s _ => by positivity)
          (le_trans hcl0 hcl)
    _ = (2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
        ring
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
