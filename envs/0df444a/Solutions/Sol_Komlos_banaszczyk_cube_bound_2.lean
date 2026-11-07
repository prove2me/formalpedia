-- Prove2me | solution 2 for Komlos.banaszczyk_cube_bound
-- status  : ACCEPTED   (prove)
-- author  : @刘柄含
-- created : 2026-11-06T06:04:44.121428+00:00
-- url     : https://prove2.me/submissions/dba0eb38-f532-4c7d-a8f3-59c5827125f7

import Definitions.Def_Komlos_model
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact
import Theorems.Thm_Komlos_bansal_jiang_komlos_bound

/-!
Banaszczyk's cube bound in the ambient dimension.

Choose fractional coefficients with vector sum zero and at most m interior
entries. Apply the Bansal–Jiang bound to subsets of those entries, then
control the error of rounding to signs by dyadic approximation.

Target https://prove2.me/theorems/9f5dd85d-203c-41f2-9245-abad0170f733
Bansal–Jiang https://prove2.me/theorems/6111c72b-15e3-401a-b4f9-801cb79df5a0
Dyadic rounding https://doi.org/10.1016/S0195-6698(86)80041-5
-/

set_option autoImplicit false

open Komlos
open scoped BigOperators

section Rounding

open Filter Set Topology

variable {ι κ : Type*} [Fintype ι]

/-- The dyadic step: an odd numerator can move one unit in either direction.
The error is measured in numerator units. -/
private theorem roundDyadic
    (v : ι → κ → ℝ) (D : ℝ)
    (hdisc : ∀ s : Finset ι, ∃ ε : ι → ℝ,
      (∀ i ∈ s, ε i = 1 ∨ ε i = -1) ∧ ∀ j, |∑ i ∈ s, ε i * v i j| ≤ D)
    (k : ℕ) (a : ι → ℕ) (ha : ∀ i, a i ≤ 2 ^ k) :
    ∃ b : ι → ℝ, (∀ i, b i = 0 ∨ b i = 1) ∧
      ∀ j, |∑ i, ((2 : ℝ) ^ k * b i - a i) * v i j| ≤ ((2 : ℝ) ^ k - 1) * D := by
  classical
  induction k generalizing a with
  | zero =>
    refine ⟨fun i => a i, ?_, ?_⟩
    · intro i
      have hi : a i ≤ 1 := by simpa using ha i
      have hz : a i = 0 ∨ a i = 1 := by omega
      rcases hz with hz | hz <;> simp [hz]
    · simp
  | succ k ih =>
    let s := Finset.univ.filter fun i => a i % 2 = 1
    obtain ⟨ε, hε, herr⟩ := hdisc s
    let a' (i : ι) := if i ∈ s ∧ ε i = 1 then a i / 2 + 1 else a i / 2
    have ha' (i : ι) : a' i ≤ 2 ^ k := by
      have hi := ha i
      rw [pow_succ] at hi
      by_cases hs : i ∈ s ∧ ε i = 1
      · have hodd : a i % 2 = 1 := by simpa [s] using hs.1
        simp only [a', if_pos hs]
        omega
      · simp only [a', if_neg hs]
        omega
    have hstep (i : ι) : 2 * (a' i : ℝ) = a i + (if i ∈ s then ε i else 0) := by
      by_cases hs : i ∈ s
      · have hodd : a i % 2 = 1 := by simpa [s] using hs
        rcases hε i hs with hp | hn
        · have hnat : 2 * (a i / 2 + 1) = a i + 1 := by omega
          simpa [a', hs, hp] using congrArg (fun z : ℕ => (z : ℝ)) hnat
        · have hnat : 2 * (a i / 2) + 1 = a i := by omega
          have hr : 2 * ((a i / 2 : ℕ) : ℝ) + 1 = (a i : ℝ) := by exact_mod_cast hnat
          norm_num [a', hs, hn]
          linarith
      · have heven : a i % 2 ≠ 1 := by simpa [s] using hs
        have hnat : 2 * (a i / 2) = a i := by omega
        simpa [a', hs] using congrArg (fun z : ℕ => (z : ℝ)) hnat
    obtain ⟨b, hb, hbound⟩ := ih a' ha'
    refine ⟨b, hb, fun j => ?_⟩
    have hsum : (∑ i, ((2 : ℝ) ^ (k + 1) * b i - a i) * v i j) =
        2 * (∑ i, ((2 : ℝ) ^ k * b i - a' i) * v i j) + ∑ i ∈ s, ε i * v i j := by
      rw [Finset.mul_sum, show s = Finset.univ.filter (fun i => i ∈ s) by simp,
        Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      have hi := hstep i
      by_cases hs : i ∈ s <;> simp [hs] at hi ⊢ <;>
        linear_combination hi * v i j
    rw [hsum]
    calc
      _ ≤ |2 * (∑ i, ((2 : ℝ) ^ k * b i - a' i) * v i j)| + |∑ i ∈ s, ε i * v i j| :=
        abs_add_le _ _
      _ ≤ 2 * (((2 : ℝ) ^ k - 1) * D) + D := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
        exacts [hbound j, herr j]
      _ = _ := by rw [pow_succ]; ring

/-- Hereditary sign discrepancy bounds the error of rounding fractional coefficients. -/
private theorem roundFractional
    (v : ι → κ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hdisc : ∀ s : Finset ι, ∃ ε : ι → ℝ,
      (∀ i ∈ s, ε i = 1 ∨ ε i = -1) ∧ ∀ j, |∑ i ∈ s, ε i * v i j| ≤ D)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Icc 0 1) :
    ∃ b : ι → ℝ, (∀ i, b i = 0 ∨ b i = 1) ∧
      ∀ j, |∑ i, (b i - x i) * v i j| ≤ D := by
  classical
  let a (k : ℕ) (i : ι) := ⌊(2 : ℝ) ^ k * x i⌋₊
  let q (k : ℕ) (i : ι) : ℝ := a k i / (2 : ℝ) ^ k
  have hfloor (k : ℕ) (i : ι) : (a k i : ℝ) ≤ (2 : ℝ) ^ k * x i :=
    Nat.floor_le (mul_nonneg (by positivity) (hx i).1)
  have ha (k : ℕ) (i : ι) : a k i ≤ 2 ^ k := by
    exact_mod_cast (hfloor k i).trans (mul_le_of_le_one_right (by positivity) (hx i).2)
  let bval (b : ι → Bool) (i : ι) : ℝ := if b i then 1 else 0
  let good (b : ι → Bool) : Set (ι → ℝ) :=
    {y | ∀ j, |∑ i, (bval b i - y i) * v i j| ≤ D}
  have hclosed (b : ι → Bool) : IsClosed (good b) := by
    rw [show good b = ⋂ j, {y : ι → ℝ | |∑ i, (bval b i - y i) * v i j| ≤ D} by
      ext y
      simp [good]]
    apply isClosed_iInter
    intro j
    apply isClosed_le _ continuous_const
    exact (continuous_finsetSum _ fun i _ =>
      (continuous_const.sub (continuous_apply i)).mul continuous_const).abs
  have hq (k : ℕ) : q k ∈ ⋃ b, good b := by
    obtain ⟨b, hb, herr⟩ := roundDyadic v D hdisc k (a k) (ha k)
    let bits (i : ι) := decide (b i = 1)
    have hbits (i : ι) : bval bits i = b i := by
      rcases hb i with hz | ho
      · norm_num [bval, bits, hz]
      · simp [bval, bits, ho]
    apply Set.mem_iUnion.mpr
    refine ⟨bits, fun j => ?_⟩
    simp only [hbits]
    have hp : 0 < (2 : ℝ) ^ k := by positivity
    have heq : (2 : ℝ) ^ k * (∑ i, (b i - q k i) * v i j) =
        ∑ i, ((2 : ℝ) ^ k * b i - a k i) * v i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [q]
      field_simp
    calc
      _ = |∑ i, ((2 : ℝ) ^ k * b i - a k i) * v i j| / (2 : ℝ) ^ k := by
        rw [← heq, abs_mul, abs_of_pos hp, mul_div_cancel_left₀ _ hp.ne']
      _ ≤ (((2 : ℝ) ^ k - 1) * D) / (2 : ℝ) ^ k := by gcongr; exact herr j
      _ ≤ D := by
        apply (div_le_iff₀ hp).2
        calc
          _ ≤ (2 : ℝ) ^ k * D := mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) hD
          _ = _ := mul_comm _ _
  have hlim : Tendsto q atTop (𝓝 x) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (g := fun k => (1 / 2 : ℝ) ^ k) ?_ (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    intro k
    have hp : 0 < (2 : ℝ) ^ k := by positivity
    have hle : q k i ≤ x i := (div_le_iff₀ hp).2 (by simpa [mul_comm] using hfloor k i)
    have hgt : (2 : ℝ) ^ k * x i < (a k i : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, div_pow, one_pow]
    apply (le_div_iff₀ hp).2
    have hqeq : q k i * (2 : ℝ) ^ k = a k i := div_mul_cancel₀ _ hp.ne'
    rw [sub_mul, hqeq]
    linarith
  have hxgood := (isClosed_iUnion_of_finite hclosed).mem_of_tendsto hlim (Eventually.of_forall hq)
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hxgood
  exact ⟨bval b, fun i => by cases b i <;> simp [bval], hb⟩

end Rounding

section Floating

open Set Filter
open scoped Topology

/-- A feasible coefficient vector with at most m interior entries. -/
private theorem exists_floating_coefficients {n m : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin m)) :
    ∃ x : Fin n → ℝ, (∀ i, x i ∈ Icc (-1) 1) ∧ (∑ i, x i • v i) = 0 ∧
      (Finset.univ.filter (fun i => x i ≠ -1 ∧ x i ≠ 1)).card ≤ m := by
  classical
  let A (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin m) := ∑ i, x i • v i
  let K := (univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) ∩ A ⁻¹' {0}
  let f (x : Fin n → ℝ) : ℝ := ∑ i, (x i) ^ 2
  have hA : Continuous A := by unfold A; fun_prop
  have hf : Continuous f := by unfold f; fun_prop
  have hcompact : IsCompact K :=
    (isCompact_univ_pi fun _ : Fin n => isCompact_Icc).inter_right
      (isClosed_singleton.preimage hA)
  have hne : K.Nonempty := by
    refine ⟨0, ⟨fun i _ => ?_, ?_⟩⟩
    · norm_num [Set.mem_Icc]
    · simp [A]
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn hne hf.continuousOn
  have hbox : ∀ i, x i ∈ Icc (-1) 1 := fun i => hx.1 i (mem_univ i)
  have hxA : A x = 0 := hx.2
  refine ⟨x, hbox, hxA, ?_⟩
  let s := Finset.univ.filter (fun i => x i ≠ -1 ∧ x i ≠ 1)
  change s.card ≤ m
  by_contra! hlarge
  have hdep : ¬ LinearIndependent ℝ (fun i : s => v i) := by
    intro hind
    have hcard := hind.fintype_card_le_finrank
    exact (not_le_of_gt hlarge) (by simpa using hcard)
  obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let d (i : Fin n) : ℝ := if h : i ∈ s then c ⟨i, h⟩ else 0
  have hd : A d = 0 := by
    unfold A
    rw [← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by simp [d, hi])]
    rw [← s.sum_attach]
    simpa [d] using hc
  have hdj : d j ≠ 0 := by simpa [d] using hj
  let y (t : ℝ) (i : Fin n) : ℝ := x i + t * d i
  have hyA (t : ℝ) : A (y t) = 0 := by
    have htd : ∑ i, (t * d i) • v i = t • A d := by
      simp only [A, Finset.smul_sum, mul_smul]
    change (∑ i, (x i + t * d i) • v i) = 0
    simp only [add_smul, Finset.sum_add_distrib]
    change A x + (∑ i, (t * d i) • v i) = 0
    rw [htd, hxA, hd, smul_zero, add_zero]
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, y t i ∈ Icc (-1) 1 := by
    apply Filter.eventually_all.2
    intro i
    by_cases hi : i ∈ s
    · have hstrict := (Finset.mem_filter.mp hi).2
      have hxi : x i ∈ Ioo (-1) 1 :=
        ⟨lt_of_le_of_ne (hbox i).1 (Ne.symm hstrict.1), lt_of_le_of_ne (hbox i).2 hstrict.2⟩
      have hcont : Continuous fun t => y t i := by unfold y; fun_prop
      have hmem : y 0 i ∈ Ioo (-1) 1 := by simpa [y] using hxi
      have h : ∀ᶠ t : ℝ in 𝓝 0, y t i ∈ Ioo (-1) 1 :=
        hcont.continuousAt (x := 0) (isOpen_Ioo.mem_nhds hmem)
      exact h.mono (fun _ ht => Ioo_subset_Icc_self ht)
    · filter_upwards [] with t
      simpa only [y, d, dif_neg hi, mul_zero, add_zero] using hbox i
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let t := δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hplus : y t ∈ K := by
    refine ⟨fun i _ => hball ?_ i, hyA t⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith
  have hminus : y (-t) ∈ K := by
    refine ⟨fun i _ => hball ?_ i, hyA (-t)⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht]
    dsimp [t]
    linarith
  have hsq : 0 < ∑ i, (t * d i) ^ 2 := by
    apply (Finset.sum_pos_iff_of_nonneg (fun i _ => sq_nonneg (t * d i))).2
    exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero (mul_ne_zero ht.ne' hdj)⟩
  have hsum : f (y t) + f (y (-t)) = 2 * f x + 2 * ∑ i, (t * d i) ^ 2 := by
    simp only [f, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by dsimp [y]; ring
  have hfp : f (y t) ≤ f x := hmax hplus
  have hfm : f (y (-t)) ≤ f x := hmax hminus
  linarith

end Floating

private theorem absorb_log_log (γ : ℝ) (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      Real.log (n + 2) ^ ((1 : ℝ) / 4) * Real.log (Real.log (n + 8)) ^ γ
        ≤ K * Real.sqrt (Real.log (n + 2)) := by
  let δ : ℝ := 1 / (4 * γ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδγ : δ * γ = 1 / 4 := by
    dsimp [δ]
    field_simp [hγ.ne']
  let K : ℝ := 3 ^ ((1 : ℝ) / 4) / δ ^ γ
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  let L : ℝ := Real.log ((n : ℝ) + 2)
  have hL : 0 < L := Real.log_pos (by linarith)
  have hshift : (n : ℝ) + 8 ≤ ((n : ℝ) + 2) ^ 3 := by
    calc
      (n : ℝ) + 8 ≤ 4 * ((n : ℝ) + 2) := by linarith
      _ ≤ ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 2) := by
        gcongr
        nlinarith [sq_nonneg (n : ℝ)]
      _ = ((n : ℝ) + 2) ^ 3 := by ring
  have hlog : Real.log ((n : ℝ) + 8) ≤ 3 * L := by
    simpa [L, Real.log_pow] using Real.log_le_log (by positivity) hshift
  have hlog_pos : 0 < Real.log ((n : ℝ) + 8) := Real.log_pos (by linarith)
  have hloglog_nonneg : 0 ≤ Real.log (Real.log ((n : ℝ) + 8)) := by
    apply Real.log_nonneg
    rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hgrowth :
      Real.log (Real.log ((n : ℝ) + 8)) ≤ (3 * L) ^ δ / δ :=
    (Real.log_le_log hlog_pos hlog).trans (Real.log_le_rpow_div (by positivity) hδ)
  change L ^ ((1 : ℝ) / 4) * Real.log (Real.log ((n : ℝ) + 8)) ^ γ ≤
    K * Real.sqrt L
  calc
    _ ≤ L ^ ((1 : ℝ) / 4) * (((3 * L) ^ δ / δ) ^ γ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hloglog_nonneg hgrowth hγ.le)
        (by positivity)
    _ = K * Real.sqrt L := by
      rw [Real.div_rpow (by positivity) hδ.le, ← Real.rpow_mul (by positivity),
        hδγ, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hL.le, Real.sqrt_eq_rpow]
      dsimp [K]
      rw [show (1 : ℝ) / 2 = 1 / 4 + 1 / 4 by norm_num, Real.rpow_add hL]
      ring

private theorem banaszczyk_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * Real.sqrt (Real.log (n + 2)) := by
  obtain ⟨C, γ, hC, hγ, hsign⟩ := Komlos.bansal_jiang_komlos_bound
  obtain ⟨K, hK, hbound⟩ := absorb_log_log γ hγ
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro n m v hv
  obtain ⟨ε, hε, hε_bound⟩ := hsign n m v hv
  refine ⟨ε, hε, fun j => (hε_bound j).trans ?_⟩
  simpa only [← mul_assoc] using mul_le_mul_of_nonneg_left (hbound n) hC.le

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * Real.sqrt (Real.log (m + 2)) := by
  classical
  obtain ⟨C, hC, hcount⟩ := banaszczyk_count_bound
  refine ⟨2 * C, by linarith, ?_⟩
  intro n m v hv
  obtain ⟨x, hx, hzero, hcard⟩ := exists_floating_coefficients v
  let s := Finset.univ.filter (fun i => x i ≠ -1 ∧ x i ≠ 1)
  let D := C * Real.sqrt (Real.log ((m : ℝ) + 2))
  have hD : 0 ≤ D := mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hsize : Fintype.card s ≤ m := by
    rw [Fintype.card_coe]
    exact hcard
  have hdisc (t : Finset s) :
      ∃ δ : s → ℝ, (∀ i ∈ t, δ i = 1 ∨ δ i = -1) ∧
        ∀ j : Fin m, |∑ i ∈ t, δ i * v i.1 j| ≤ D := by
    let e := Fintype.equivFin t
    obtain ⟨δ, hδ, hbound⟩ := hcount (Fintype.card t) m
      (fun k => v (e.symm k).1.1) (fun k => hv (e.symm k).1.1)
    let sign : s → ℝ := fun i => if hi : i ∈ t then δ (e ⟨i, hi⟩) else 1
    refine ⟨sign, fun i hi => ?_, fun j => ?_⟩
    · simpa [sign, hi] using hδ (e ⟨i, hi⟩)
    have hsum : (∑ i ∈ t, sign i * v i.1 j) =
        ∑ k, δ k * v (e.symm k).1.1 j := by
      rw [← Finset.sum_attach]
      simpa [sign] using
        (e.sum_comp (fun k => δ k * v (e.symm k).1.1 j))
    have htm : Fintype.card t ≤ m := by
      exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans hsize
    have hlog : Real.log ((Fintype.card t : ℝ) + 2) ≤ Real.log ((m : ℝ) + 2) := by
      apply Real.log_le_log
      · positivity
      · exact add_le_add_left (Nat.cast_le.mpr htm) 2
    rw [hsum]
    exact (hbound j).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlog) hC.le)
  let y : s → ℝ := fun i => (x i.1 + 1) / 2
  have hy (i : s) : y i ∈ Set.Icc 0 1 :=
    ⟨by dsimp [y]; linarith [(hx i.1).1], by dsimp [y]; linarith [(hx i.1).2]⟩
  obtain ⟨b, hb, hbound⟩ :=
    roundFractional (fun (i : s) (j : Fin m) => v i.1 j) D hD hdisc y hy
  let ε : Fin n → ℝ := fun i => if hi : i ∈ s then 2 * b ⟨i, hi⟩ - 1 else x i
  refine ⟨ε, fun i => ?_, fun j => ?_⟩
  · by_cases hi : i ∈ s
    · rcases hb ⟨i, hi⟩ with h | h
      · right
        norm_num [ε, hi, h]
      · left
        norm_num [ε, hi, h]
    · simp only [ε, dif_neg hi]
      by_contra! h
      apply hi
      simp [s, h.1, h.2]
  have hzero_j : (∑ i, x i * v i j) = 0 := by
    simpa only [map_sum, PiLp.projₗ_apply, PiLp.smul_apply, smul_eq_mul, map_zero] using
      congrArg (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) j) hzero
  have hdiff : (∑ i, (ε i - x i) * v i j) =
      2 * ∑ i : s, (b i - y i) * v i.1 j := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ i ∈ s, (ε i - x i) * v i j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        simp [ε, hi]
      _ = ∑ i : s, (ε i.1 - x i.1) * v i.1 j := by
        rw [← Finset.sum_attach]
        rfl
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := i.2
        simp only [ε, hi, dite_true, y]
        ring
  have hsum : (∑ i, ε i * v i j) = 2 * ∑ i : s, (b i - y i) * v i.1 j := by
    simpa only [sub_mul, Finset.sum_sub_distrib, hzero_j, sub_zero] using hdiff
  rw [hsum, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
  exact mul_le_mul_of_nonneg_left (hbound j) (by norm_num)
