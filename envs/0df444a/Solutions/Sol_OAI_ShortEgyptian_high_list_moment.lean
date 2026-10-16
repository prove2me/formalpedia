-- Prove2me | solution 1 for OAI.ShortEgyptian.high_list_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:57:58.992219+00:00
-- url     : https://prove2.me/submissions/46668b22-6bf4-4525-9eac-53bc3f3ccc54

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DeterministicLists.lean:L129-L167
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.high_list_moment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Theorems.Thm_OAI_ShortEgyptian_phase_second_moment
import Theorems.Thm_OAI_ShortEgyptian_reciprocal_phase_long_interval

-- ---- from OAI.NumberTheory.ShortEgyptian.DeterministicLists ----
namespace OAI

universe uA

namespace ShortEgyptian

open scoped BigOperators
open Finset Filter

lemma nat_dist_one {a b : ℕ} (hab : a ≠ b) : 1 ≤ |(a:ℝ)-b| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have hle : (a:ℝ) ≤ b := by exact_mod_cast h.le
    rw [abs_of_nonpos (by linarith : (a:ℝ)-b ≤ 0)]
    have hh : (a:ℝ)+1 ≤ b := by exact_mod_cast h
    linarith
  · have hle : (b:ℝ) ≤ a := by exact_mod_cast h.le
    rw [abs_of_nonneg (by linarith : 0 ≤ (a:ℝ)-b)]
    have hh : (b:ℝ)+1 ≤ a := by exact_mod_cast h
    linarith

lemma deterministic_list_moment {A : Type uA} [Fintype A] [Nonempty A]
    (t : A → ℕ) (hinj : Function.Injective t) (W Z T : ℝ) (p q B : ℕ)
    (hZ : 0 ≤ Z) (hB : 4 ≤ B) (hT : 1 ≤ T) (hp : 1 ≤ p)
    (ht : ∀ i, (t i:ℝ) ≤ W)
    (hlarge : (reciprocalConstantNat B:ℝ)*T^reciprocalPower B ≤ p)
    (hZlo : (q:ℝ)^4 ≤ Z) (hZhi : Z*W ≤ (p:ℝ)^B) :
    (∑ u ∈ Icc p q, ‖(∑ i, phase (Z*t i/u))/(Fintype.card A:ℂ)‖^2) ≤
      (q:ℝ)/Fintype.card A+16*q/T := by
  have hcorr (i j : A) (hij : i ≠ j) :
      ‖∑ u ∈ Icc p q, phase (Z*t i/u)*(starRingEnd ℂ) (phase (Z*t j/u))‖ ≤ 16*q/T := by
    have hd1 : 1 ≤ |(t i:ℝ)-t j| := nat_dist_one (fun h => hij (hinj h))
    have ht0 (k : A) : (0:ℝ) ≤ t k := Nat.cast_nonneg _
    have hdW : |(t i:ℝ)-t j| ≤ W := by
      apply abs_le.mpr
      constructor <;> linarith [ht i,ht j,ht0 i,ht0 j]
    have heq (u : ℕ) : phase (Z*t i/u)*(starRingEnd ℂ) (phase (Z*t j/u)) =
        phase ((Z*((t i:ℝ)-t j))/u) := by
      rw [←phase_sub]
      congr 1
      ring
    simp_rw [heq]
    apply reciprocal_phase_long_interval B T _ p q hB hT hp hlarge
    · rw [abs_mul,abs_of_nonneg hZ]
      exact hZlo.trans (by nlinarith)
    · rw [abs_mul,abs_of_nonneg hZ]
      exact (mul_le_mul_of_nonneg_left hdW hZ).trans hZhi
  have hh := phase_second_moment (Icc p q) (fun i u => phase (Z*t i/u))
    (fun _ _ => phase_norm _) (16*q/T) (by positivity) hcorr
  apply hh.trans
  gcongr
  rw [Nat.card_Icc]
  exact_mod_cast (show q+1-p ≤ q by omega)

lemma deterministic_moment_scalar (m : ℕ) (hm : 100 ≤ (m:ℝ)) :
    (1:ℝ)/2^m + (1/2:ℝ)*Real.exp (-(1/50:ℝ)*m) ≤ Real.exp (-(1/100:ℝ)*m) := by
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpow : (1:ℝ)/2^m ≤ (1/2:ℝ)*Real.exp (-(1/100:ℝ)*m) := by
    rw [←Real.exp_log (by positivity : (0:ℝ)<(2:ℝ)^m),Real.log_pow,one_div,←Real.exp_neg]
    have hgap : (2:ℝ) ≤ Real.exp ((49/100:ℝ)*m) := by
      have hh := Real.add_one_le_exp ((49/100:ℝ)*m)
      linarith
    have hh := mul_le_mul_of_nonneg_right hgap (Real.exp_nonneg (-(1/2:ℝ)*m))
    rw [←Real.exp_add] at hh
    have hE : (49/100:ℝ)*m+(-(1/2:ℝ)*m) = -(1/100:ℝ)*m := by ring
    rw [hE] at hh
    have hh' : Real.exp (-(m:ℝ)*Real.log 2) ≤ Real.exp (-(1/2:ℝ)*m) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [neg_mul] at hh'
    linarith
  have hdec : Real.exp (-(1/50:ℝ)*m) ≤ Real.exp (-(1/100:ℝ)*m) := Real.exp_le_exp.mpr (by nlinarith only [hm])
  linarith

lemma deterministic_cutoff_lower (S X : ℝ) (m : ℕ) (hS : 0 ≤ S)
    (hmS : (m:ℝ) ≤ S) (hX : Real.exp S ≤ X) :
    Real.exp ((9/10:ℝ)*S) ≤ (⌊X*Real.exp (-(1/10000:ℝ)*m)⌋₊+1:ℕ) := by
  have hh : Real.exp ((9/10:ℝ)*S) ≤ X*Real.exp (-(1/10000:ℝ)*m) := by
    calc
      _ ≤ Real.exp (S-(1/10000:ℝ)*m) := Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp S*Real.exp (-(1/10000:ℝ)*m) := by rw [sub_eq_add_neg,Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hX (Real.exp_nonneg _)
  have hf := Nat.lt_floor_add_one (X*Real.exp (-(1/10000:ℝ)*m))
  simpa only [Nat.cast_add, Nat.cast_one] using hh.trans hf.le

lemma deterministic_T_scale (S : ℝ) (m P : ℕ) (K : ℝ) (hS : 0 < S)
    (hlog : 1 ≤ Real.log S) (hm : (m:ℝ) ≤ S/Real.log S)
    (hP : (P:ℝ) ≤ Real.log S)
    (hconst : K*32^P ≤ Real.exp (S/4)) :
    K*(32*Real.exp ((1/50:ℝ)*m))^P ≤ Real.exp ((9/10:ℝ)*S) := by
  have hL : 0 < Real.log S := by linarith
  have hmS : (m:ℝ)*Real.log S ≤ S := (le_div_iff₀ hL).mp hm
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hPm : (P:ℝ)*(m:ℝ) ≤ S := by nlinarith [hm0]
  rw [mul_pow,←Real.exp_nat_mul]
  calc
    _ = (K*32^P)*Real.exp ((P:ℝ)*((1/50:ℝ)*m)) := by ring
    _ ≤ Real.exp (S/4)*Real.exp ((1/50:ℝ)*S) := by
      apply mul_le_mul hconst (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (S/4+(1/50:ℝ)*S) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

lemma deterministic_phase_bounds (S X : ℝ) (D m C l : ℕ) (hS : 0 ≤ S)
    (hD : 1000 ≤ D) (hmS : (m:ℝ) ≤ S)
    (hX : Real.exp S ≤ X) (hXD : X ≤ Real.exp ((D:ℝ)/4*S))
    (hClo : Real.exp ((D:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(D:ℝ)*S))
    (hl : 1 ≤ l) (hlhi : (l:ℝ) ≤ Real.exp ((1/2500:ℝ)*m)) :
    (⌊X⌋₊:ℝ)^4 ≤ (l:ℝ)*C ∧
    (l:ℝ)*C*Real.exp (101*S) ≤ (⌊X*Real.exp (-(1/10000:ℝ)*m)⌋₊+1:ℕ)^(3*D) := by
  have hX0 : 0 ≤ X := (Real.exp_nonneg _).trans hX
  have hC0 : (0:ℝ) ≤ C := Nat.cast_nonneg _
  have hl1 : (1:ℝ) ≤ l := by exact_mod_cast hl
  constructor
  · calc
      _ ≤ (Real.exp ((D:ℝ)/4*S))^4 := pow_le_pow_left₀ (by positivity) ((Nat.floor_le hX0).trans hXD) 4
      _ = Real.exp ((D:ℝ)*S) := by rw [←Real.exp_nat_mul]; congr 1; push_cast; ring
      _ ≤ (C:ℝ) := hClo
      _ ≤ _ := by nlinarith
  · have hlo := deterministic_cutoff_lower S X m hS hmS hX
    have hlS : (l:ℝ) ≤ Real.exp S := hlhi.trans (Real.exp_le_exp.mpr (by nlinarith))
    have hDN : (1000:ℝ) ≤ D := by exact_mod_cast hD
    calc
      _ ≤ Real.exp S*Real.exp (2*(D:ℝ)*S)*Real.exp (101*S) := by gcongr
      _ = Real.exp ((2*(D:ℝ)+102)*S) := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((9/10:ℝ)*S*(3*(D:ℝ))) := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (by linarith : 0 ≤ (7:ℝ)*D-1020) hS])
      _ = (Real.exp ((9/10:ℝ)*S))^(3*D) := by rw [←Real.exp_nat_mul]; congr 1; push_cast; ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hlo _

lemma high_list_moment {A : Type uA} [Fintype A] [Nonempty A]
    (S X : ℝ) (D m C l : ℕ) (t : A → ℕ) (hinj : Function.Injective t)
    (hcard : Fintype.card A = 2^m) (ht : ∀ i, (t i:ℝ) ≤ Real.exp (101*S))
    (hS : 0 < S) (hlog : 1 ≤ Real.log S) (hD : 1000 ≤ D)
    (hm : (m:ℝ) ≤ S/Real.log S) (hm100 : 100 ≤ (m:ℝ))
    (hP : (reciprocalPower (3*D):ℝ) ≤ Real.log S)
    (hconst : (reciprocalConstantNat (3*D):ℝ)*32^reciprocalPower (3*D) ≤ Real.exp (S/4))
    (hX : Real.exp S ≤ X) (hXD : X ≤ Real.exp ((D:ℝ)/4*S))
    (hClo : Real.exp ((D:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(D:ℝ)*S))
    (hl : 1 ≤ l) (hlhi : (l:ℝ) ≤ Real.exp ((1/2500:ℝ)*m)) :
    (∑ u ∈ Icc (⌊X*Real.exp (-(1/10000:ℝ)*m)⌋₊+1) ⌊X⌋₊,
      ‖(∑ i, phase ((l:ℝ)*C*t i/u))/(Fintype.card A:ℂ)‖^2) ≤
      X*Real.exp (-(1/100:ℝ)*m) := by
  let T := 32*Real.exp ((1/50:ℝ)*m)
  have hmS : (m:ℝ) ≤ S := hm.trans (div_le_self hS.le hlog)
  have hT : 1 ≤ T := by
    have hh : 1 ≤ Real.exp ((1/50:ℝ)*m) := Real.one_le_exp (by positivity)
    dsimp [T]
    linarith
  have hlarge := (deterministic_T_scale S m (reciprocalPower (3*D)) (reciprocalConstantNat (3*D))
    hS hlog hm hP hconst).trans (deterministic_cutoff_lower S X m hS.le hmS hX)
  have hZ := deterministic_phase_bounds S X D m C l hS.le hD hmS hX hXD hClo hChi hl hlhi
  have hh := deterministic_list_moment t hinj (Real.exp (101*S)) ((l:ℝ)*C) T
    (⌊X*Real.exp (-(1/10000:ℝ)*m)⌋₊+1) ⌊X⌋₊ (3*D)
    (by positivity) (by omega) hT (by omega) ht hlarge hZ.1 hZ.2
  apply hh.trans
  have hX0 : 0 ≤ X := (Real.exp_nonneg _).trans hX
  have hq : (⌊X⌋₊:ℝ) ≤ X := Nat.floor_le hX0
  have hTpos : 0 < T := by linarith
  have hden : (0:ℝ) < 2^m := by positivity
  rw [hcard,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ X/(2:ℝ)^m+16*X/T := by gcongr
    _ = X*((1:ℝ)/2^m+(1/2:ℝ)*Real.exp (-(1/50:ℝ)*m)) := by
      dsimp [T]
      rw [neg_mul, Real.exp_neg]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (deterministic_moment_scalar m hm100) hX0

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Filter


theorem solution.{uA} : type_of% @_root_.OAI.ShortEgyptian.high_list_moment.{uA} := @_root_.OAI.ShortEgyptian.high_list_moment.{uA}
