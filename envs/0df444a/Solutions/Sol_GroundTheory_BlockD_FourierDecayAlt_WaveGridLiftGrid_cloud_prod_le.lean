-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:49:28.682801+00:00
-- url     : https://prove2.me/submissions/67f77523-d7ce-41fa-857f-28fb26699ea8

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_CloudProd
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_weight_prod
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_factor_le
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_prod_le_prod_range_of_rank
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_gap_sum

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
theorem _root_.solution (k : ℕ) (lam : ℕ → ℝ) (c g Y : ℝ) (hk : 1 ≤ k) (hc : 0 ≤ c) (hg : 1 + c ≤ g)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s) :
    ∏ s ∈ Icc 1 (k - 1), (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) ^ 2 * (k : ℝ) ^ 2 := by
  classical
  have hF0 : ∀ s, 0 ≤ 1 + (1 + c) / max |Y + lam s| 1 := fun s => by
    have : 0 ≤ (1 + c) / max |Y + lam s| 1 :=
      div_nonneg (by linarith) (le_trans zero_le_one (le_max_right _ _))
    linarith
  have hw : ∀ j : ℕ, 1 ≤ (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) := fun j => by
    split_ifs
    · linarith
    · have : (0 : ℝ) ≤ 1 / (j : ℝ) := by positivity
      linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hW : ∏ j ∈ range k, (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) = (2 + c) * k := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [cloud_weight_prod]
    push_cast
    ring
  have hone : (1 : ℝ) ≤ (2 + c) * k := by nlinarith
  rw [← prod_filter_mul_prod_filter_not (Icc 1 (k - 1)) (fun s => 0 < Y + lam s)]
  have hL : ∏ s ∈ (Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s),
      (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) * k := by
    by_cases hne : ((Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s)).Nonempty
    · have ht := max'_mem _ hne
      set t := ((Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s)).max' hne with ht_def
      rw [mem_filter, mem_Icc] at ht
      rw [← hW]
      apply prod_le_prod_range_of_rank _ _ (fun s => t - s) _ k (fun s _ => hF0 s) _ _ _ hw
      · intro s hs
        have hst : s ≤ t := le_max' _ _ hs
        rw [mem_filter, mem_Icc] at hs
        apply cloud_factor_le c g _ _ hc hg
        have h1 := cloud_gap_sum k lam g hgap s hs.1.1 t hst ht.1.2
        have h2 := le_abs_self (Y + lam s)
        show (((t - s : ℕ) : ℝ)) * g ≤ |Y + lam s|
        rw [Nat.cast_sub hst]
        linarith [ht.2]
      · intro a ha b hb hab
        have ha' : a ≤ t := le_max' _ _ (mem_coe.mp ha)
        have hb' : b ≤ t := le_max' _ _ (mem_coe.mp hb)
        simp only at hab
        omega
      · intro s hs
        have hst : s ≤ t := le_max' _ _ hs
        show t - s < k
        omega
    · rw [not_nonempty_iff_eq_empty.mp hne, prod_empty]
      exact hone
  have hR : ∏ s ∈ (Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s),
      (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) * k := by
    by_cases hne : ((Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s)).Nonempty
    · have hu := min'_mem _ hne
      set u := ((Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s)).min' hne with hu_def
      rw [mem_filter, mem_Icc] at hu
      rw [← hW]
      apply prod_le_prod_range_of_rank _ _ (fun s => s - u) _ k (fun s _ => hF0 s) _ _ _ hw
      · intro s hs
        have hus : u ≤ s := min'_le _ _ hs
        rw [mem_filter, mem_Icc] at hs
        apply cloud_factor_le c g _ _ hc hg
        have h1 := cloud_gap_sum k lam g hgap u hu.1.1 s hus hs.1.2
        have h2 := neg_le_abs (Y + lam s)
        show (((s - u : ℕ) : ℝ)) * g ≤ |Y + lam s|
        rw [Nat.cast_sub hus]
        have := not_lt.mp hu.2
        linarith
      · intro a ha b hb hab
        have ha' : u ≤ a := min'_le _ _ (mem_coe.mp ha)
        have hb' : u ≤ b := min'_le _ _ (mem_coe.mp hb)
        simp only at hab
        omega
      · intro s hs
        have hus : u ≤ s := min'_le _ _ hs
        rw [mem_filter, mem_Icc] at hs
        show s - u < k
        omega
    · rw [not_nonempty_iff_eq_empty.mp hne, prod_empty]
      exact hone
  calc _ ≤ ((2 + c) * k) * ((2 + c) * k) :=
        mul_le_mul hL hR (prod_nonneg fun s _ => hF0 s) (by linarith)
    _ = (2 + c) ^ 2 * (k : ℝ) ^ 2 := by ring
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
