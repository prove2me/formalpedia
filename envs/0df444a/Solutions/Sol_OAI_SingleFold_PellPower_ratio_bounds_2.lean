-- Prove2me | solution 2 for OAI.SingleFold.PellPower.ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:34:33.022179+00:00
-- url     : https://prove2.me/submissions/93dba22f-9df8-4bf0-b314-157fefb79a74

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Pell.lean:L88-L120
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PellPower.ratio_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell

-- ---- from OAI.NumberTheory.SingleFold.Pell ----
namespace OAI

namespace SingleFold.PellPower

variable {a : ℕ} (ha : 1 < a)

lemma y_positive {n : ℕ} (hn : 0 < n) : 0 < Pell.yn ha n :=
  lt_of_lt_of_le hn (Pell.yn_ge_n ha n)

lemma step_bounds (n : ℕ) :
    (2*a-1)*Pell.yn ha (n+1) ≤ Pell.yn ha (n+2) ∧
    Pell.yn ha (n+2) ≤ (2*a)*Pell.yn ha (n+1) := by
  have hr := Pell.yn_succ_succ ha n
  have hm := (Pell.strictMono_y ha).monotone (Nat.le_succ n)
  have ha' : 2*a-1+1=2*a := by omega
  constructor <;> nlinarith

lemma rate_bounds (n : ℕ) : 2*(a:ℝ)-1 ≤ rate ha n ∧ rate ha n ≤ 2*a := by
  have hp : (0:ℝ) < Pell.yn ha (n+1) := by exact_mod_cast y_positive ha (by omega : 0<n+1)
  simp only [rate]
  rw [le_div_iff₀ hp,div_le_iff₀ hp]
  have hb := step_bounds ha n
  have ha' : 1 ≤ 2*a := by omega
  constructor
  · have hc : ((2*a-1:ℕ):ℝ)=2*(a:ℝ)-1 := by rw [Nat.cast_sub ha']; push_cast; rfl
    rw [←hc]; exact_mod_cast hb.1
  · exact_mod_cast hb.2

lemma rate_pos (n : ℕ) : 0 < rate ha n := by
  have hh := (rate_bounds ha n).1
  have ha' : (1:ℝ)<a := by exact_mod_cast ha
  linarith

lemma rate_zero : rate ha 0 = 2*a := by
  have hh := Pell.yn_succ_succ ha 0
  norm_num only [Pell.yn_zero,Pell.yn_one,add_zero,mul_one] at hh
  simp only [rate,zero_add,Pell.yn_one,hh,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,div_one]

lemma rate_succ (n : ℕ) : rate ha (n+1)=2*a-1/rate ha n := by
  have hr := Pell.yn_succ_succ ha (n+1)
  have hr' : (Pell.yn ha (n+3):ℝ)+Pell.yn ha (n+1)=2*a*Pell.yn ha (n+2) := by exact_mod_cast hr
  have hp : (Pell.yn ha (n+1):ℝ) ≠ 0 := by exact_mod_cast (y_positive ha (by omega : 0<n+1)).ne'
  have hp' : (Pell.yn ha (n+2):ℝ) ≠ 0 := by exact_mod_cast (y_positive ha (by omega : 0<n+2)).ne'
  simp only [rate]
  have hn : n+1+2=n+3 := by omega
  rw [hn]
  rw [one_div_div]
  apply (div_eq_iff hp').mpr
  rw [sub_mul,div_mul_cancel₀ _ hp']
  linarith only [hr']

lemma ratio_rate {b u : ℕ} (hb : 1 < b) (hu : 1 < u) (n : ℕ) :
    (b:ℝ)*rate hu n ≤ rate (show 1 < b*u by nlinarith) n := by
  have hbu : 1 < b*u := by nlinarith
  have hb' : (1:ℝ)<b := by exact_mod_cast hb
  induction n with
  | zero => simp only [rate_zero,Nat.cast_mul]; ring_nf; rfl
  | succ n hn =>
    rw [rate_succ,rate_succ]
    have hp := rate_pos hu n
    have hp' := rate_pos hbu n
    have hh : 1/rate hbu n ≤ (b:ℝ)/rate hu n := by
      rw [div_le_div_iff₀ hp' hp]
      nlinarith
    simp only [Nat.cast_mul,div_eq_mul_inv,one_mul] at hh ⊢
    nlinarith only [hh]

lemma ratio_bounds {b u : ℕ} (hb : 1 < b) (hu : 1 < u) (n : ℕ) :
    (b:ℝ)^n ≤ (Pell.yn (show 1 < b*u by nlinarith) (n+1):ℝ)/Pell.yn hu (n+1) ∧
    (Pell.yn (show 1 < b*u by nlinarith) (n+1):ℝ)/Pell.yn hu (n+1) ≤
      (b:ℝ)^n*(1+1/(2*u-1))^n := by
  have hbu : 1 < b*u := by nlinarith
  have hu' : (1:ℝ)<u := by exact_mod_cast hu
  have hb' : (1:ℝ)<b := by exact_mod_cast hb
  have hd : 0 < 2*(u:ℝ)-1 := by linarith
  induction n with
  | zero => simp
  | succ n hn =>
    have hp : (0:ℝ)<Pell.yn hu (n+1) := by exact_mod_cast y_positive hu (by omega : 0<n+1)
    have hp' : (0:ℝ)<Pell.yn hbu (n+1) := by exact_mod_cast y_positive hbu (by omega : 0<n+1)
    have hrp := rate_pos hu n
    have hrp' := rate_pos hbu n
    have he : (Pell.yn hbu (n+2):ℝ)/Pell.yn hu (n+2) =
        (rate hbu n/rate hu n)*((Pell.yn hbu (n+1):ℝ)/Pell.yn hu (n+1)) := by
      simp only [rate]
      field_simp
    have hl : (b:ℝ) ≤ rate hbu n/rate hu n := (le_div_iff₀ hrp).mpr (ratio_rate hb hu n)
    have hh : rate hbu n/rate hu n ≤ (b:ℝ)*(1+1/(2*u-1)) := by
      have hstep := (rate_bounds hbu n).2
      have hstep' := (rate_bounds hu n).1
      calc
        _ ≤ (2*(b*u:ℕ):ℝ)/(2*u-1) := div_le_div₀ (by positivity) hstep hd hstep'
        _ = (b:ℝ)*(1+1/(2*u-1)) := by push_cast; field_simp; ring
    rw [he,pow_succ',pow_succ']
    constructor
    · exact mul_le_mul hl hn.1 (by positivity) (by positivity)
    · calc
        _ ≤ ((b:ℝ)*(1+1/(2*u-1)))*((b:ℝ)^n*(1+1/(2*u-1))^n) :=
          mul_le_mul hh hn.2 (by positivity) (by positivity)
        _ = _ := by ring

end SingleFold.PellPower

namespace SingleFold.PellAnalytics
end SingleFold.PellAnalytics

namespace SingleFold.PellSystem
end SingleFold.PellSystem

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PellPower


theorem solution : type_of% @_root_.OAI.SingleFold.PellPower.ratio_bounds := @_root_.OAI.SingleFold.PellPower.ratio_bounds
