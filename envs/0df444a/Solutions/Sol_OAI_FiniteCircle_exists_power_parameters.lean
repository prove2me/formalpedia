-- Prove2me | solution 1 for OAI.FiniteCircle.exists_power_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:07:29.098846+00:00
-- url     : https://prove2.me/submissions/41e4eeb9-f1b2-482b-940b-71c5f7111f1e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/UpperParameters.lean:L48-L166
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.exists_power_parameters. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Histograms
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Separation

-- ---- from OAI.Combinatorics.FiniteCircle.UpperParameters ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem log_large_aux {t : ℝ} (ht : 16 ≤ t) :
    1 ≤ Real.log t ∧ 4 * Real.log t ≤ t := by
  have ht0 : 0 < t := by linarith
  have hl16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]
    norm_num
  have hl2lo : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2hi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlo := Real.log_le_log (by norm_num : (0:ℝ) < 16) ht
  rw [hl16] at hlo
  refine ⟨by linarith, ?_⟩
  have hr := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num) : 0 < t/16)
  rw [Real.log_div ht0.ne' (by norm_num), hl16] at hr
  linarith

theorem natLog_le_twice_log (n : ℕ) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have h := Real.natLog_le_logb n 2
  simp only [Real.logb, Nat.cast_ofNat] at h
  have hl : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl0 : 0 < Real.log 2 := by linarith
  have hn := Real.log_natCast_nonneg n
  refine h.trans ((div_le_iff₀ hl0).mpr ?_)
  nlinarith

theorem exists_power_parameters {d : ℕ} (hd : 16 ≤ Real.log d) :
    ∃ b H : ℕ, 2 ≤ b ∧ 1 ≤ H ∧ d ≤ b^H ∧
      (4 * (b:ℝ) * (1024 * ((Nat.log 2 (b^H) : ℝ)+1)^2)^H) ≤
        Real.exp (32 * Real.sqrt (Real.log d * Real.log (Real.log d))) := by
  let t := Real.log d
  let l := Real.log t
  have ht : 16 ≤ t := hd
  obtain ⟨hl, hlt⟩ := log_large_aux ht
  change 1 ≤ l at hl
  change 4*l ≤ t at hlt
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < l := by linarith
  let r := Real.sqrt (t/l)
  let s := Real.sqrt (t*l)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr2 : r^2 = t/l := Real.sq_sqrt (div_nonneg ht0.le hl0.le)
  have hs2 : s^2 = t*l := Real.sq_sqrt (mul_nonneg ht0.le hl0.le)
  have hrl : r^2*l = t := by rw [hr2]; field_simp
  have hrlo : 2 ≤ r := by
    have h : (4:ℝ) ≤ t/l := (le_div_iff₀ hl0).mpr (by linarith)
    nlinarith only [h, hr2, hr0]
  have hrhi : r ≤ t := by
    have h : t/l ≤ t := div_le_self ht0.le hl
    nlinarith only [h, hr2, hr0, ht]
  have hrs : r*l = s := by
    have hsq : (r*l)^2 = s^2 := by
      calc
        _ = (r^2*l)*l := by ring
        _ = t*l := by rw [hrl]
        _ = _ := hs2.symm
    have hp : 0 ≤ r*l := mul_nonneg hr0 hl0.le
    nlinarith only [hsq, hp, hs0]
  have htr : t = r*s := by rw [← hrs, ← hrl]; ring
  have hslo : 1 ≤ s := by nlinarith only [hs2, hs0, ht, hl]
  let H := ⌊r⌋₊
  have hHhi : (H:ℝ) ≤ r := Nat.floor_le hr0
  have hHlow : r < (H:ℝ)+1 := Nat.lt_floor_add_one r
  have hHhalf : r/2 ≤ (H:ℝ) := by linarith
  have hHpos : 0 < (H:ℝ) := by linarith
  have hHnat : 1 ≤ H := by exact_mod_cast (show (1:ℝ) ≤ H by linarith only [hrlo, hHhalf])
  let b := ⌈Real.exp (t/H)⌉₊
  have hbexp : Real.exp (t/H) ≤ (b:ℝ) := Nat.le_ceil _
  have hbupper : (b:ℝ) ≤ 2 * Real.exp (t/H) := by
    have hc : (b:ℝ) < Real.exp (t/H)+1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    have he : 1 ≤ Real.exp (t/H) := Real.one_le_exp_iff.mpr (div_nonneg ht0.le hHpos.le)
    linarith
  have hb2 : 2 ≤ b := by
    have he : 1 < Real.exp (t/H) := Real.one_lt_exp_iff.mpr (div_pos ht0 hHpos)
    have hb1 : (1:ℝ) < b := he.trans_le hbexp
    exact_mod_cast hb1
  have hb0 : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hlblo : t/H ≤ Real.log b := by
    have h := Real.log_le_log (Real.exp_pos _) hbexp
    simpa only [Real.log_exp] using h
  have hlbhi : Real.log b ≤ 1 + t/H := by
    have h := Real.log_le_log hb0 hbupper
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h
    linarith [Real.log_two_lt_d9]
  let n := b^H
  have hn0 : (0:ℝ) < n := by dsimp [n]; positivity
  have hlogn : Real.log n = (H:ℝ)*Real.log b := by simp [n, Real.log_pow]
  have htn : t ≤ Real.log n := by
    rw [hlogn]
    calc
      _ = (H:ℝ)*(t/H) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlblo hHpos.le
  have hnt : Real.log n ≤ 2*t := by
    rw [hlogn]
    have h := mul_le_mul_of_nonneg_left hlbhi hHpos.le
    have he : (H:ℝ)*(1+t/H) = H+t := by field_simp
    rw [he] at h
    linarith
  have hd0 : (0:ℝ) < d := by
    by_contra h
    have hd0 : d = 0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg d))
    norm_num [hd0] at hd
  have hdn : d ≤ n := by
    exact_mod_cast (Real.log_le_log_iff hd0 hn0).mp htn
  let K : ℝ := (Nat.log 2 n : ℝ)+1
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hKbound : K ≤ 5*t := by
    have h := natLog_le_twice_log n
    dsimp [K]
    linarith
  have hlogK : Real.log K ≤ 4+l := by
    have h := Real.log_le_log hKpos hKbound
    rw [Real.log_mul (by norm_num) ht0.ne'] at h
    have h5 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5)
    dsimp [l]
    linarith
  let B : ℝ := 1024*K^2
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hlogB : Real.log B ≤ 20*l := by
    have h1024 : Real.log 1024 = 10 * Real.log 2 := by
      rw [show (1024:ℝ)=2^10 by norm_num, Real.log_pow]
      norm_num
    dsimp [B]
    rw [Real.log_mul (by norm_num) (pow_pos hKpos 2).ne', Real.log_pow, h1024]
    norm_num
    linarith only [hlogK, hl, Real.log_two_lt_d9]
  have hdiv : t/(H:ℝ) ≤ 2*s := by
    apply (div_le_iff₀ hHpos).mpr
    rw [htr]
    nlinarith only [hHhalf, hs0]
  have hHl : (H:ℝ)*l ≤ s := by rw [← hrs]; exact mul_le_mul_of_nonneg_right hHhi hl0.le
  have hprodpos : 0 < 4*(b:ℝ)*B^H := by positivity
  have hlogprod : Real.log (4*(b:ℝ)*B^H) ≤ 32*s := by
    rw [Real.log_mul (by positivity) (pow_pos hBpos H).ne',
      Real.log_mul (by norm_num) hb0.ne', Real.log_pow]
    have h4 : Real.log 4 ≤ 2 := by
      rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [Real.log_two_lt_d9]
    have h := mul_le_mul_of_nonneg_left hlogB hHpos.le
    nlinarith only [h4, hlbhi, hdiv, h, hHl, hslo]
  refine ⟨b, H, hb2, hHnat, hdn, ?_⟩
  change 4*(b:ℝ)*B^H ≤ Real.exp (32*s)
  exact (Real.log_le_iff_le_exp hprodpos).mp hlogprod

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.exists_power_parameters := @_root_.OAI.FiniteCircle.exists_power_parameters
