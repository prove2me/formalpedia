-- Prove2me | solution 1 for OAI.FiniteCircle.all_length_inversion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:43:56.963344+00:00
-- url     : https://prove2.me/submissions/7255bc15-fa21-4352-822e-844b3992d98e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Lower.lean:L95-L112
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.all_length_inversion. The node keeps its source
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

-- ---- from OAI.Combinatorics.FiniteCircle.Lower ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

 theorem log_lowerCap {n : ℕ} : Real.log (lowerCap n) = 128*(n:ℝ)^8*Real.log n := by
  simp only [lowerCap,Nat.cast_pow,Real.log_pow,Nat.cast_mul,Nat.cast_ofNat]
  ring

 theorem cap_log_bound {q d : ℕ} (hq : 500000≤q) (hd0 : 2≤d)
    (hd : d<lowerCap (2*(q+1))) :
    Real.log (d:ℝ) ≤ 65536*((2*q:ℕ):ℝ)^8*Real.log (2*q:ℕ) := by
  let n : ℝ := (2*q:ℕ)
  let n' : ℝ := (2*(q+1):ℕ)
  have hn : (1000000:ℝ)≤n := by dsimp [n]; exact_mod_cast (show 1000000≤2*q by omega)
  have hn0 : 0<n := by linarith
  have hn' : 1≤n' := by dsimp [n']; exact_mod_cast (show 1≤2*(q+1) by omega)
  have hnn : n'≤2*n := by dsimp [n,n']; exact_mod_cast (show 2*(q+1)≤2*(2*q) by omega)
  have hl2 : Real.log 2≤Real.log n := Real.log_le_log (by norm_num) (by linarith)
  have hln' : Real.log n'≤2*Real.log n := by
    calc
      _ ≤ Real.log (2*n) := Real.log_le_log (by linarith) hnn
      _ = Real.log 2+Real.log n := Real.log_mul (by norm_num) hn0.ne'
      _ ≤ _ := by linarith
  calc
    _ ≤ Real.log (lowerCap (2*(q+1))) := Real.log_le_log (by exact_mod_cast (show 0<d by omega))
      (by exact_mod_cast hd.le)
    _ = 128*(n')^8*Real.log n' := log_lowerCap
    _ ≤ 128*(2*n)^8*(2*Real.log n) := mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hnn 8) (by norm_num))
      hln' (Real.log_nonneg hn') (by positivity)
    _ = _ := by ring

 theorem cap_loglog_bound {n t : ℝ} (hn : 1000000≤n) (ht : 0<t)
    (hb : t≤65536*n^8*Real.log n) : Real.log t≤32*Real.log n := by
  have hn0 : 0<n := by linarith
  have hln : 0<Real.log n := Real.log_pos (by linarith)
  have hc := Real.log_le_log ht hb
  have he : Real.log (65536*n^8*Real.log n) = Real.log 65536+8*Real.log n+Real.log (Real.log n) := by
    rw [Real.log_mul (by positivity) hln.ne',Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'),Real.log_pow]
    norm_num
  rw [he] at hc
  have hconst : Real.log 65536≤Real.log n := Real.log_le_log (by norm_num) (by linarith)
  have hl := Real.log_le_sub_one_of_pos hln
  linarith

 theorem scale_bound_of_logs {n : ℝ} {d : ℕ} (hn : 1≤n) (hd : 2≤d)
    (hc : Real.log (d:ℝ) ≤ 65536*n^8*Real.log n)
    (hl : Real.log (Real.log (d:ℝ))≤32*Real.log n) :
    exponentScale d≤2048*n^4*Real.log n := by
  have hln := Real.log_nonneg hn
  have hld : 0≤Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤d by omega))
  have hprod : Real.log (d:ℝ)*Real.log (Real.log (d:ℝ)) ≤ (2048*n^4*Real.log n)^2 := by
    calc
      _ ≤ Real.log (d:ℝ)*(32*Real.log n) := mul_le_mul_of_nonneg_left hl hld
      _ ≤ (65536*n^8*Real.log n)*(32*Real.log n) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 2097152*(n^4*Real.log n)^2 := by ring
      _ ≤ 4194304*(n^4*Real.log n)^2 := mul_le_mul_of_nonneg_right
        (show (2097152:ℝ)≤4194304 by norm_num) (sq_nonneg (n^4*Real.log n))
      _ = _ := by ring
  exact Real.sqrt_le_iff.mpr ⟨by positivity,hprod⟩

 theorem all_length_inversion {q d : ℕ} (hq : 500000≤q) (hd0 : 2≤d)
    (hd : d<lowerCap (2*(q+1))) :
    Real.exp ((1/8192)*exponentScale d) ≤ ((2*q:ℕ):ℝ)^(4*q^4) := by
  let n : ℝ := (2*q:ℕ)
  have hn : (1000000:ℝ)≤n := by dsimp [n]; exact_mod_cast (show 1000000≤2*q by omega)
  have hn0 : 0<n := by linarith
  have hc := cap_log_bound hq hd0 hd
  have hl := cap_loglog_bound hn (Real.log_pos (show 1<(d:ℝ) by exact_mod_cast (show 1<d by omega))) hc
  have hs := scale_bound_of_logs (show 1≤n by linarith) hd0 hc hl
  have hr : (1/8192)*exponentScale d ≤ (4*q^4:ℕ)*Real.log n := by
    calc
      _ ≤ (1/8192)*(2048*n^4*Real.log n) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = _ := by dsimp [n]; push_cast; ring
  calc
    _ ≤ Real.exp (Real.log (n^(4*q^4))) := by
      apply Real.exp_le_exp.mpr
      simpa only [Real.log_pow] using hr
    _ = _ := Real.exp_log (pow_pos hn0 _)

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.all_length_inversion := @_root_.OAI.FiniteCircle.all_length_inversion
