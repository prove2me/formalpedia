-- Prove2me | solution 1 for OAI.FiniteCircle.lower_coefficient_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:55:38.17075+00:00
-- url     : https://prove2.me/submissions/ba454b71-e816-43a3-9a74-8087ff67dbed

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Parameters.lean:L216-L272
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.lower_coefficient_budget. The node keeps its source
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

-- ---- from OAI.Combinatorics.FiniteCircle.Parameters ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem lower_coefficient_budget {n k J : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    (hJ : J≤n^13) :
    (n:ℝ)^k * (4*(n^4:ℕ)/((n^4:ℕ):ℝ)^(2*n^4)+
        2*J/(((n^4:ℕ):ℝ)/2)^(n^4)) ≤ (1/268435456)/(n:ℝ)^(3*n^4) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hnp : (0:ℝ)<n := lt_of_lt_of_le zero_lt_one hn1
  have hk16 : 16≤k := by
    have hh : 64≤n^4 := by
      have ht := Nat.pow_le_pow_left (show 3≤n by omega) 4
      norm_num at ht ⊢
      omega
    omega
  have hp : 0<(n:ℝ)^(14*k) := pow_pos hnp _
  have hn4 : (n:ℝ)^4≤(n:ℝ)^13 := pow_le_pow_right₀ hn1 (by norm_num)
  have h14 : (n:ℝ)^(14*k) ≤ ((n^4:ℕ):ℝ)^(2*n^4) := by
    push_cast
    rw [← pow_mul]
    apply pow_le_pow_right₀ hn1
    omega
  have hbbase : (n:ℝ)^7 ≤ (((n^4:ℕ):ℝ)/2)^2 := by
    have hn4r : (4:ℝ)≤n := by exact_mod_cast (show 4≤n by omega)
    have ht := mul_le_mul_of_nonneg_right hn4r (pow_nonneg hnp.le 7)
    push_cast
    nlinarith [show (n:ℝ)*(n:ℝ)^7=(n:ℝ)^8 by ring]
  have hb : (n:ℝ)^(14*k) ≤ (((n^4:ℕ):ℝ)/2)^(n^4) := by
    calc
      _ = ((n:ℝ)^7)^(2*k) := by rw [← pow_mul]; congr 1; ring
      _ ≤ ((((n^4:ℕ):ℝ)/2)^2)^(2*k) := pow_le_pow_left₀ (by positivity) hbbase _
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hc : (4*((n^4:ℕ):ℝ)/((n^4:ℕ):ℝ)^(2*n^4)+
      2*(J:ℝ)/(((n^4:ℕ):ℝ)/2)^(n^4)) ≤ 6*(n:ℝ)^13/(n:ℝ)^(14*k) := by
    have hJr : (J:ℝ)≤(n:ℝ)^13 := by exact_mod_cast hJ
    calc
      _ ≤ (4*(n:ℝ)^13)/(n:ℝ)^(14*k)+(2*(n:ℝ)^13)/(n:ℝ)^(14*k) := by
        apply add_le_add
        · exact div_le_div₀ (by positivity) (by push_cast; linarith) hp h14
        · exact div_le_div₀ (by positivity) (by linarith) hp hb
      _ = _ := by ring
  have hconst : (6*268435456:ℝ)≤(n:ℝ)^3 := by
    have hr : (1000000:ℝ)≤n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n:ℝ)-1000000)]
  have hpow : (6*268435456:ℝ)*(n:ℝ)^(13*k+13) ≤ (n:ℝ)^(14*k) := by
    calc
      _ ≤ (n:ℝ)^3*(n:ℝ)^(13*k+13) := mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = (n:ℝ)^(13*k+16) := by rw [← pow_add]; congr 1; ring
      _ ≤ _ := pow_le_pow_right₀ hn1 (by omega)
  have hlast : (n:ℝ)^k*(6*(n:ℝ)^13/(n:ℝ)^(14*k)) ≤ (1/268435456)/(n:ℝ)^(3*n^4) := by
    apply (le_div_iff₀ (pow_pos hnp _)).mpr
    rw [div_eq_mul_inv]
    have he : (n:ℝ)^k*(6*(n:ℝ)^13*((n:ℝ)^(14*k))⁻¹)*(n:ℝ)^(3*n^4) =
        6*(n:ℝ)^(13*k+13)/(n:ℝ)^(14*k) := by
      rw [hk]
      ring
    rw [he]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans hlast

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.lower_coefficient_budget := @_root_.OAI.FiniteCircle.lower_coefficient_budget
