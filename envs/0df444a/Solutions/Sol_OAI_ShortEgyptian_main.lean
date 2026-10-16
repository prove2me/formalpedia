-- Prove2me | solution 1 for OAI.ShortEgyptian.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:15:16.006111+00:00
-- url     : https://prove2.me/submissions/ed88016e-bc37-4c30-9b36-f44539611455

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/Main.lean:L33-L52
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ShortEgyptian.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ShortEgyptian_main) verbatim and is proved by it.
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_UpperAssembly
import Theorems.Thm_OAI_ShortEgyptian_denominator_bound_aux
import Theorems.Thm_OAI_ShortEgyptian_density_unrolled
import Theorems.Thm_OAI_ShortEgyptian_depth_bound
import Theorems.Thm_OAI_ShortEgyptian_eventually_density_numeric
import Theorems.Thm_OAI_ShortEgyptian_eventually_log_pow_le
import Theorems.Thm_OAI_ShortEgyptian_eventually_scaleM_large
import Theorems.Thm_OAI_ShortEgyptian_exists_expansion
import Theorems.Thm_OAI_ShortEgyptian_exists_residueSystem
import Theorems.Thm_OAI_ShortEgyptian_uniform_divisor_moment
import Theorems.Thm_OAI_ShortEgyptian_upper_at_scale

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem isExpansion_iff (a b : ℕ) (ns : List ℕ) :
    IsExpansion a b ns ↔ ns.Pairwise (· < ·) ∧
      (∀ n ∈ ns, 2 ≤ n) ∧ unitSum ns = (a : ℚ) / b := by
  have heq : (ns.map (fun n => (1 : ℚ) / (n : ℚ))).sum = unitSum ns := by
    induction ns with
    | nil => rfl
    | cons n ns ih => simpa [unitSum] using congrArg ((1 : ℚ) / (n : ℚ) + ·) ih
  simp only [IsExpansion, heq]

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.GreedyExistence ----
namespace OAI

namespace ShortEgyptian

theorem minLength_attained {a b : ℕ} (hab : a < b) :
    ∃ ns : List ℕ, IsExpansion a b ns ∧ ns.length = minLength a b := by
  obtain ⟨ns, hns⟩ := exists_expansion a b hab
  have hex : {k : ℕ | ∃ ns : List ℕ, IsExpansion a b ns ∧ ns.length = k}.Nonempty :=
    ⟨ns.length, ns, hns, rfl⟩
  exact Nat.sInf_mem hex

theorem minLength_le {a b : ℕ} {ns : List ℕ} (hns : IsExpansion a b ns) :
    minLength a b ≤ ns.length := Nat.sInf_le ⟨ns, hns, rfl⟩

theorem minLength_le_maxMinLength {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    minLength a b ≤ maxMinLength b := by
  unfold maxMinLength
  exact Finset.le_sup (f := fun a : ℕ => minLength a b) (Finset.mem_Ico.mpr ⟨ha, hab⟩)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.LowerBound ----
namespace OAI

namespace ShortEgyptian

theorem denominator_bound (ns : List ℕ) (hpos : ∀ n ∈ ns, 0 < n)
    (heq : unitSum ns = 1) {n : ℕ} (hn : n ∈ ns) :
    n ≤ ns.length ^ (2 ^ (ns.length - 1)) := by
  let sorted := ns.mergeSort (fun a b => decide (a ≤ b))
  have hperm : sorted.Perm ns := List.mergeSort_perm ns _
  have hpair : sorted.Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
        (by intros; simp_all; omega) (by intros; simp; omega) ns
  have hsp : ∀ d ∈ sorted, 0 < d := fun d hd => hpos d (hperm.mem_iff.mp hd)
  have hsum : unitSum sorted = (1 : ℚ) / (1 : ℕ) := by
    have hh := (hperm.map (fun n : ℕ => (1 : ℚ) / n)).sum_eq
    simpa [unitSum, heq] using hh.trans heq
  have hh := denominator_bound_aux sorted hpair hsp 1 1 ns.length
    (by omega) (by omega) (by simp [sorted]) hsum n (hperm.mem_iff.mpr hn)
  simpa [sorted] using hh

theorem hard_numerator_bound {b : ℕ} (hb : 2 ≤ b) {ns : List ℕ}
    (he : IsExpansion (b - 1) b ns) :
    b ≤ (ns.length + 1) ^ (2 ^ ns.length) := by
  have hbpos : 0 < b := by omega
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hbpos
  rw [isExpansion_iff] at he
  have hh : unitSum (b :: ns) = 1 := by
    rw [unitSum_cons, he.2.2, Nat.cast_sub (by omega : 1 ≤ b)]
    push_cast
    field_simp
    ring
  have hh' := denominator_bound (b :: ns)
    (by
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact hbpos
      · exact lt_of_lt_of_le (by omega : 0 < 2) (he.2.1 n hn)) hh (by simp : b ∈ b :: ns)
  simpa using hh'

theorem expansion_length_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {ns : List ℕ} (he : IsExpansion a b ns) : 0 < ns.length := by
  rw [isExpansion_iff] at he
  by_contra hh
  have hnil : ns = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
  rw [hnil, unitSum_nil] at he
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have := div_pos haQ hbQ
  linarith [he.2.2]

theorem loglog_le_twice_length {b : ℕ} (hb : 2 ≤ b) {ns : List ℕ}
    (he : IsExpansion (b - 1) b ns) :
    Real.log (Real.log (b : ℝ)) ≤ 2 * (ns.length : ℝ) := by
  let k := ns.length
  have hk : 0 < k := expansion_length_pos (by omega : 0 < b - 1) (by omega) he
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k + 1 := by positivity
  have hlogk : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hh : (b : ℝ) ≤ ((k : ℝ) + 1) ^ (2 ^ k) := by
    exact_mod_cast hard_numerator_bound hb he
  have hfirst := Real.log_le_log (lt_trans (by norm_num : (0 : ℝ) < 1) hbR) hh
  rw [Real.log_pow] at hfirst
  have hsecond := Real.log_le_log (Real.log_pos hbR) hfirst
  rw [Real.log_mul (by positivity) (ne_of_gt hlogk)] at hsecond
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hsecond
  have ht : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlt := Real.log_le_self (le_of_lt hlogk)
  have hlk := Real.log_le_sub_one_of_pos hkp
  have hm := mul_le_mul_of_nonneg_left ht (le_of_lt hkR)
  calc
    Real.log (Real.log (b : ℝ)) ≤ (k : ℝ) * Real.log 2 + Real.log (Real.log ((k : ℝ) + 1)) := hsecond
    _ ≤ 2 * (ns.length : ℝ) := by dsimp [k] at *; nlinarith

theorem main_lower (b : ℕ) (hb : 2 ≤ b) :
    (1 / 2 : ℝ) * Real.log (Real.log (b : ℝ)) ≤ (maxMinLength b : ℝ) := by
  obtain ⟨ns, he, hlen⟩ := minLength_attained (show b - 1 < b by omega)
  have hh := loglog_le_twice_length hb he
  have hk := minLength_le_maxMinLength (show 1 ≤ b - 1 by omega) (show b - 1 < b by omega)
  rw [hlen] at hh
  have hkR : (minLength (b - 1) b : ℝ) ≤ maxMinLength b := by exact_mod_cast hk
  linarith

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ParameterBounds ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem reciprocalConstant_pos (r : ℕ) : 0 < reciprocalConstantNat r := by
  unfold reciprocalConstantNat
  positivity

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

lemma scaleM_bounds (S : ℝ) (hlog : 1 ≤ Real.log S) (hS : 4*Real.log S ≤ S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧
      (scaleM S:ℝ) ≤ S := by
  have hl : 0 < Real.log S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hf := Nat.sub_one_lt_floor (S/Real.log S)
  have hu := Nat.floor_le (div_nonneg hS0 hl.le)
  have hx : 4 ≤ S/Real.log S := (le_div_iff₀ hl).mpr (by linarith)
  refine ⟨?_,hu,hu.trans (div_le_self hS0 hlog)⟩
  dsimp [scaleM]
  have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
  rw [heq]
  linarith

lemma level_pos (S : ℝ) (j : ℕ) : 0 < level S j := Real.exp_pos _
lemma level_zero (S : ℝ) : level S 0 = Real.exp ((dimX:ℝ)*S) := by simp [level]

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleBounds ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open Filter Topology

lemma eventually_depth_tail :
    ∀ᶠ S : ℝ in atTop,
      (depth S:ℝ)*Real.exp (-(1/250:ℝ)*scaleM S) < 1/2 := by
  let K : ℝ := 3*(dimX:ℝ)*10000
  have hK : 0 < K := by norm_num [K,dimX,dimM]
  filter_upwards [eventually_scaleM_large 500,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_log_pow_le 4 1 (by norm_num : (0:ℝ)<1),eventually_ge_atTop (4*K),
    eventually_gt_atTop (0:ℝ)] with S hm hL hbig hSK hS
  rw [Real.rpow_one,pow_one] at hbig
  have hb : 4*Real.log S ≤ S := by linarith
  have hmb := scaleM_bounds S hL hb
  have hd := depth_bound S hS hL hmb.1 hmb.2.2
  have hE : Real.exp (-(1/250:ℝ)*scaleM S) ≤ 1/S^2 := by
    calc
      _ ≤ Real.exp (-(2*Real.log S)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg,two_mul,Real.exp_add,Real.exp_log hS]; simp [pow_two]
  have hLS : Real.log S ≤ S := by have hh := Real.log_le_sub_one_of_pos hS; linarith
  calc
    _ ≤ (K*S)*(1/S^2) := mul_le_mul (hd.trans (mul_le_mul_of_nonneg_left hLS hK.le)) hE
      (Real.exp_nonneg _) (by positivity)
    _ = K/S := by field_simp
    _ ≤ 1/4 := (div_le_iff₀ hS).mpr (by linarith)
    _ < _ := by norm_num

lemma eventually_ListScale : ∀ᶠ S : ℝ in atTop, ListScale S := by
  let A : ℝ := (reciprocalConstantNat (3*dimC):ℝ)*32^reciprocalPower (3*dimC)
  have hA : 0 < A := mul_pos (by exact_mod_cast reciprocalConstant_pos (3*dimC)) (by positivity)
  filter_upwards [eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 100,
    eventually_log_pow_le 100001 1 (by norm_num : (0:ℝ)<1),eventually_scaleM_large 1000000,
    Real.tendsto_log_atTop.eventually_ge_atTop (reciprocalPower (3*dimC):ℝ),
    eventually_ge_atTop (4*Real.log A),eventually_depth_tail]
    with S hS hlog hbig hm hP hA' hd
  rw [Real.rpow_one,pow_one] at hbig
  refine ⟨hS,hlog,by linarith,hm,hP,?_,hd⟩
  exact (Real.log_le_iff_le_exp hA).mp (by linarith)

lemma ListScale.log_one {S : ℝ} (h : ListScale S) : 1 ≤ Real.log S := by linarith [h.log_large]
lemma ListScale.S_pos {S : ℝ} (h : ListScale S) : 0 < S := by linarith [h.two_le]
lemma ListScale.m_bounds {S : ℝ} (h : ListScale S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧ (scaleM S:ℝ) ≤ S :=
  scaleM_bounds S h.log_one (by linarith [h.log_bound,h.log_large])
end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.TerminalScale ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma terminalLength_bound (S : ℝ) (hlog : 1 ≤ Real.log S) :
    (terminalLength S:ℝ) ≤ terminalConstant*Real.log S := by
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < Real.log (10000/9999:ℝ) := Real.log_pos (by norm_num)
  have ha := Nat.ceil_lt_add_one (show 0 ≤ 100000*Real.log S/Real.log 2 by positivity)
  have hk := Nat.ceil_lt_add_one (show 0 ≤ Real.log S/Real.log (10000/9999:ℝ) by positivity)
  dsimp [terminalLength,binaryExponent,terminalSteps,terminalConstant]
  push_cast
  ring_nf at ha hk ⊢
  linarith

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DescentSets ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma mem_levelBad (S : ℝ) (M C K j u : ℕ) :
    u ∈ levelBad S M C K j ↔ 0 < u ∧ (u:ℝ) ≤ level S j ∧
      ¬HasUnitSum M (levelMultiplier S C j) u (K+(depth S-j)) := by
  constructor
  · intro hu
    obtain ⟨hu,hn⟩ := mem_filter.mp hu
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hu
    exact ⟨by omega,(Nat.cast_le.mpr hhi).trans (Nat.floor_le (level_pos S j).le),hn⟩
  · rintro ⟨hu0,hu,hn⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hu0,Nat.le_floor hu⟩,hn⟩

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.MomentRecurrence ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter

lemma eventually_MomentScale : ∀ᶠ S : ℝ in atTop, MomentScale S :=
  uniform_divisor_moment _ (by norm_num [momentDimension,dimC,dimX,dimM]) descentR

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.Density ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

lemma densityConstant_pos : 0 < densityConstant := by
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < Real.log (10000/9999:ℝ) := Real.log_pos (by norm_num)
  dsimp [densityConstant,terminalConstant]
  positivity

lemma density_from_residueSystem (S : ℝ) (h : ListScale S) (hm : MomentScale S) (hq : 2 ≤ S^(1/4:ℝ))
    (hnum : (depth S:ℝ)*Real.exp (2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ))) ≤ 1/8)
    (C : ℕ) (R : ResidueSystem S C) (hClo : Real.exp ((dimC:ℝ)*S) ≤ C)
    (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) : Nonempty (DenseData S C) := by
  let H := levelBad S R.M C (terminalLength S) 0
  let U := Icc 1 ⌊Real.exp ((dimX:ℝ)*S)⌋₊
  let G := U \ H
  have hden := (density_unrolled S h hm hq C R hClo hChi).trans hnum
  have hH : (H.card:ℝ) ≤ Real.exp ((dimX:ℝ)*S)/8 := by
    have hh := (div_le_iff₀ (level_pos S 0)).mp hden
    simpa only [H,level_zero,div_eq_mul_inv,mul_comm,one_mul] using hh
  have hmul : levelMultiplier S C 0=C := by
    apply ite_eq_left
    rw [level_zero]
    apply Real.exp_lt_exp.mpr
    have hD : (1:ℝ)<dimX := by norm_num [dimX,dimM]
    nlinarith [h.S_pos]
  refine ⟨⟨R.M,G,R.M_lower,R.M_upper,sdiff_subset,?_,?_⟩⟩
  · apply le_trans _ hH
    apply Nat.cast_le.mpr
    apply card_le_card
    intro u hu
    obtain ⟨hu,hug⟩ := mem_sdiff.mp hu
    by_contra huh
    exact hug (mem_sdiff.mpr ⟨hu,huh⟩)
  · intro u hu
    obtain ⟨hu,hn⟩ := mem_sdiff.mp hu
    have hu' := mem_Icc.mp hu
    have huR : (u:ℝ) ≤ level S 0 := by
      rw [level_zero]
      exact (Nat.cast_le.mpr hu'.2).trans (Nat.floor_le (Real.exp_nonneg _))
    have hex : HasUnitSum R.M C u (terminalLength S+depth S) := by
      by_contra he
      apply hn
      apply (mem_levelBad S R.M C _ 0 u).mpr
      exact ⟨hu'.1,huR,by simpa only [hmul,Nat.sub_zero] using he⟩
    obtain ⟨ns,hns,hlen⟩ := hex
    refine ⟨ns,hns,?_⟩
    have hh : (ns.length:ℝ) ≤ ((terminalLength S+depth S:ℕ):ℝ) := by exact_mod_cast hlen
    push_cast at hh
    have ht := terminalLength_bound S h.log_one
    have hd := depth_bound S h.S_pos h.log_one h.m_bounds.1 h.m_bounds.2.2
    dsimp [densityConstant]
    nlinarith

lemma eventually_density : ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
    Real.exp ((dimC:ℝ)*S) ≤ C → (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S) → Nonempty (DenseData S C) := by
  filter_upwards [eventually_ListScale,eventually_MomentScale,eventually_density_numeric,
    eventually_log_pow_le 2 0 (by norm_num : (0:ℝ)<1/4)] with S h hm hnum hq
  simp only [pow_zero,mul_one] at hq
  intro C hClo hChi
  obtain ⟨R⟩ := exists_residueSystem S h C hClo hChi
  exact density_from_residueSystem S h hm hq hnum C R hClo hChi

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.GreedyPreparation ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

lemma greedyConstant_pos : 0<greedyConstant := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  dsimp [greedyConstant]
  have hD : (0:ℝ)<dimC := by norm_num [dimC,dimX,dimM]
  positivity

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.UpperAssembly ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

lemma upperConstant_pos : 0<upperConstant := by
  dsimp [upperConstant]
  linarith [greedyConstant_pos,densityConstant_pos]

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.Main ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open Finset Filter Topology

lemma eventually_upper_at_scale : ∀ᶠ S : ℝ in atTop, ∀ a b : ℕ, 1≤a → a<b → (b:ℝ)=Real.exp S →
    ∃ ns, IsExpansion a b ns ∧ (ns.length:ℝ)≤upperConstant*Real.log S := by
  filter_upwards [eventually_density,eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with S hd hS hlog
  intro a b ha hab hb
  exact upper_at_scale S hS hlog hd a b ha hab hb

theorem main_upper_expansions : ∃ b₀ : ℕ, 2≤b₀ ∧ ∀ b : ℕ, b₀≤b → ∀ a : ℕ, 1≤a → a<b →
    ∃ ns, IsExpansion a b ns ∧ (ns.length:ℝ)≤upperConstant*Real.log (Real.log (b:ℝ)) := by
  obtain ⟨S₀,hS₀⟩ := eventually_atTop.mp eventually_upper_at_scale
  let b₀ := max 2 ⌈Real.exp S₀⌉₊
  refine ⟨b₀,le_max_left _ _,?_⟩
  intro b hb a ha hab
  have hb2 : 2≤b := (le_max_left _ _).trans hb
  have hbp : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hbexp : Real.exp S₀ ≤ (b:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hb))
  have hlog : S₀ ≤ Real.log b := by
    have hh := Real.log_le_log (Real.exp_pos S₀) hbexp
    simpa only [Real.log_exp] using hh
  exact hS₀ (Real.log b) hlog a b ha hab (Real.exp_log hbp).symm

theorem main :
    (∀ a b : ℕ, 1 ≤ a → a < b → ∃ ns : List ℕ, IsExpansion a b ns) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ b : ℕ, b₀ ≤ b →
        c₁ * Real.log (Real.log (b : ℝ)) ≤ (maxMinLength b : ℝ) ∧
        (maxMinLength b : ℝ) ≤ c₂ * Real.log (Real.log (b : ℝ)) := by
  refine ⟨fun a b _ hab => exists_expansion a b hab,1/2,upperConstant,by norm_num,upperConstant_pos,?_⟩
  obtain ⟨b₀,hb₀,hupper⟩ := main_upper_expansions
  refine ⟨b₀,hb₀,?_⟩
  intro b hb
  have hb2 : 2≤b := hb₀.trans hb
  refine ⟨main_lower b hb2,?_⟩
  have hne : (Ico 1 b).Nonempty := ⟨1,mem_Ico.mpr ⟨le_rfl,by omega⟩⟩
  obtain ⟨a,ha,heq⟩ := exists_mem_eq_sup (Ico 1 b) hne (fun a => minLength a b)
  obtain ⟨ha,hab⟩ := mem_Ico.mp ha
  obtain ⟨ns,hns,hlen⟩ := hupper b hb a ha hab
  have hh : (minLength a b:ℝ)≤ns.length := by exact_mod_cast minLength_le hns
  have hmax : maxMinLength b=minLength a b := heq
  rw [hmax]
  exact hh.trans hlen

end ShortEgyptian

end OAI

-- ---- mission target ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open Finset Filter Topology

theorem solution :
    (∀ a b : ℕ, 1 ≤ a → a < b → ∃ ns : List ℕ, IsExpansion a b ns) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ b : ℕ, b₀ ≤ b →
        c₁ * Real.log (Real.log (b : ℝ)) ≤ (maxMinLength b : ℝ) ∧
        (maxMinLength b : ℝ) ≤ c₂ * Real.log (Real.log (b : ℝ)) := by
  first
    | exact OAI.ShortEgyptian.main
    | (apply OAI.ShortEgyptian.main <;> assumption)
    | (intros; apply OAI.ShortEgyptian.main <;> assumption)
