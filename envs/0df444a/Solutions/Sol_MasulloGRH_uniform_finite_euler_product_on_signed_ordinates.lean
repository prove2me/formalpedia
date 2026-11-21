-- Prove2me | solution 1 for MasulloGRH.uniform_finite_euler_product_on_signed_ordinates
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:01:43.871922+00:00
-- url     : https://prove2.me/submissions/6029a740-6d42-4ed0-aeb8-8621a0657154

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Int
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

open Finset Complex

/-- A finite grid with more samples than places contains a sample whose
Euler factor stays uniformly away from zero at every place. -/
theorem finite_grid_euler_factor_separation
    {V J : Type*} [Fintype V] [Fintype J]
    (hcard : Fintype.card V < Fintype.card J) (phase : V → J → ℂ) (δ : ℝ)
    (hsep : ∀ v i j, i ≠ j → 2 * δ ≤ ‖phase v i - phase v j‖) :
    ∃ j, ∀ v, δ ≤ ‖1 - phase v j‖ := by
  classical
  by_contra! h
  choose bad hbad using h
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt bad hcard
  have hi := hbad i
  have hj := hbad j
  rw [← heq] at hj
  have htri := dist_triangle_left (phase (bad i) i) (phase (bad i) j) 1
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
  linarith [hsep (bad i) i j hij]

/-- A lower bound for the unit-circle factor persists on every nonnegative ray
with at most a factor of two loss. -/
theorem unit_euler_factor_radial_bound (z : ℂ) (hz : ‖z‖ = 1) (r : ℝ) (hr : 0 ≤ r) :
    ‖1 - z‖ ≤ 2 * ‖1 - (r : ℂ) * z‖ := by
  have hrev : |1 - r| ≤ ‖1 - (r : ℂ) * z‖ := by
    simpa only [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, hz, mul_one]
      using abs_norm_sub_norm_le (1 : ℂ) ((r : ℂ) * z)
  have hdiff : ‖z - (r : ℂ) * z‖ = |1 - r| := by
    rw [show z - (r : ℂ) * z = ((1 - r : ℝ) : ℂ) * z by push_cast; rw [sub_mul, one_mul],
        norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one]
  have htri := dist_triangle_right (1 : ℂ) z ((r : ℂ) * z)
  simp only [dist_eq_norm, hdiff] at htri
  linarith

theorem euler_factor_cpow_radial_bound (q : ℝ) (hq : 0 < q)
    (t σ : ℝ) (a : ℂ) (ha : ‖a‖ = 1) :
    ‖1 - a * Complex.exp (((-t * Real.log q : ℝ) : ℂ) * Complex.I)‖ ≤
      2 * ‖1 - a * (q : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ := by
  let z := a * Complex.exp (((-t * Real.log q : ℝ) : ℂ) * Complex.I)
  let r := Real.exp (-σ * Real.log q)
  have hz : ‖z‖ = 1 := by simp [z, ha, Complex.norm_exp]
  have hfactor : a * (q : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) = (r : ℂ) * z := by
    have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    dsimp [r,z]
    rw [Complex.cpow_def_of_ne_zero hqc, ← Complex.ofReal_log hq.le, Complex.ofReal_exp]
    conv_rhs => rw [← mul_assoc, mul_comm _ a, mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfactor]
  exact unit_euler_factor_radial_bound z hz r (Real.exp_pos _).le

/-- Good ordinates in each unit cell give the corrected signed indexing,
without requiring the exceptional ordinate zero to be good. -/
theorem good_ordinates_of_unit_intervals (Good : ℝ → Prop)
    (h : ∀ k : ℤ, ∃ t : ℝ, (k : ℝ) ≤ t ∧ t ≤ (k : ℝ) + 1 ∧ Good t) :
    ∃ T : ℤ → ℝ, (∀ k : ℤ, T k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) ∧ (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
      (∀ k, T k ≤ T (k + 1)) ∧
      Filter.Tendsto (fun k => |T k|) Filter.cofinite Filter.atTop ∧ ∀ k, Good (T k) := by
  choose T hlow hupp hgood using h
  refine ⟨T, fun k => ⟨hlow k, hupp k⟩, ?_, ?_, ?_, ?_, hgood⟩
  · intro k hk
    have hk' : 0 ≤ (k : ℝ) := by exact_mod_cast hk
    exact hk'.trans (hlow k)
  · intro k hk
    have hk' : k + 1 ≤ 0 := by omega
    have hkr : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast hk'
    exact (hupp k).trans hkr
  · intro k
    exact (hupp k).trans (by simpa using hlow (k + 1))
  · have hlim : Filter.Tendsto (fun k : ℤ => |(k : ℝ)|) Filter.cofinite Filter.atTop := by
      simpa [Function.comp_def, Real.norm_eq_abs] using
        tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.tendsto_atTop.mp hlim (b + 1)] with k hk
    have hl := hlow k
    have hu := hupp k
    rcases le_total (0 : ℝ) k with hkpos | hkneg
    · rw [abs_of_nonneg hkpos] at hk
      linarith [le_abs_self (T k)]
    · rw [abs_of_nonpos hkneg] at hk
      linarith [neg_le_abs (T k)]

-- A bound common to all pairs of distinct samples and all places.
private theorem finite_ordinate_separation {m : ℕ} (phase : Fin m → Fin (m+1) → ℂ)
    (hinj : ∀ v, Function.Injective (phase v)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v j k, j ≠ k → 2 * δ ≤ ‖phase v j - phase v k‖ := by
  classical
  let d (p : Fin m × Fin (m+1) × Fin (m+1)) : ℝ :=
    if p.2.1 = p.2.2 then 1 else ‖phase p.1 p.2.1 - phase p.1 p.2.2‖
  let S := insert 1 (Finset.univ.image d)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self ..⟩
  let b := S.min' hS
  have hb : 0 < b := by
    have hmem : b ∈ S := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hmem with h | h
    · linarith
    · rcases Finset.mem_image.mp h with ⟨⟨v,j,k⟩, _, heq⟩
      rw [← heq]
      dsimp [d]
      split_ifs with he
      · norm_num
      · exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun e => he (hinj v e)))
  refine ⟨b / 2, by positivity, ?_⟩
  intro v j k hjk
  have hmem : d (v,j,k) ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(v,j,k), Finset.mem_univ _, rfl⟩)
  have hle := Finset.min'_le _ _ hmem
  simp [d,hjk] at hle
  dsimp [b]
  linarith

private theorem uniform_ordinate_grid {m : ℕ} (freq : Fin m → ℝ) (hfreq : ∀ i, 0 < freq i)
    {L : ℝ} (hL : 0 < L) :
    ∃ h : ℝ, 0 < h ∧ (m : ℝ) * h ≤ L ∧
      ∀ i, Function.Injective (fun j : Fin (m+1) =>
        Complex.exp (((j.val : ℝ) * h * freq i : ℝ) * Complex.I)) := by
  let B : ℝ := (∑ i, freq i) + 1
  have hsum : 0 ≤ ∑ i, freq i := Finset.sum_nonneg (fun i _ => (hfreq i).le)
  have hB : 0 < B := by dsimp [B]; linarith
  have hBi (i) : freq i ≤ B := by
    have hle : freq i ≤ ∑ i, freq i :=
      Finset.single_le_sum (fun j _ => (hfreq j).le) (Finset.mem_univ i)
    dsimp [B]; linarith
  let M : ℝ := m + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let h : ℝ := min (L / M) (Real.pi / (M * B))
  have hh : 0 < h := lt_min (div_pos hL hM) (div_pos Real.pi_pos (mul_pos hM hB))
  have h1 : h * M ≤ L := (le_div_iff₀ hM).mp (min_le_left ..)
  have h2 : h * (M * B) ≤ Real.pi := (le_div_iff₀ (mul_pos hM hB)).mp (min_le_right ..)
  refine ⟨h,hh,?_,?_⟩
  · have hm : (m : ℝ) ≤ M := by dsimp [M]; linarith
    linarith [mul_le_mul_of_nonneg_right hm hh.le]
  intro i j k heq
  have hb (n : Fin (m+1)) : (n.val : ℝ) * h * freq i ≤ Real.pi := by
    have hn : (n.val : ℝ) ≤ M := by dsimp [M]; exact_mod_cast n.isLt.le
    calc
      _ ≤ M * h * B := mul_le_mul (mul_le_mul_of_nonneg_right hn hh.le) (hBi i)
        (hfreq i).le (mul_nonneg hM.le hh.le)
      _ = h * (M * B) := by ring
      _ ≤ _ := h2
  have hn (n : Fin (m+1)) : 0 ≤ (n.val : ℝ) * h * freq i := by have := hfreq i; positivity
  have hr := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (((j.val : ℝ) * h * freq i : ℝ) : ℂ) * Complex.I)
    (y := (((k.val : ℝ) * h * freq i : ℝ) : ℂ) * Complex.I)
    (by simpa using (lt_of_lt_of_le (neg_lt_zero.mpr Real.pi_pos) (hn j)))
    (by simpa using hb j)
    (by simpa using (lt_of_lt_of_le (neg_lt_zero.mpr Real.pi_pos) (hn k)))
    (by simpa using hb k) heq
  have hr' := congrArg Complex.im hr
  simp [hh.ne', (hfreq i).ne'] at hr'
  exact Fin.ext hr'

private theorem ordinate_in_every_interval {m : ℕ} (freq : Fin m → ℝ)
    (hfreq : ∀ i, 0 < freq i) {L : ℝ} (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℝ) (z : Fin m → ℂ), (∀ i, ‖z i‖ = 1) →
      ∃ t ∈ Set.Icc a (a + L), ∀ i,
        δ ≤ ‖1 - z i * Complex.exp (((-t * freq i : ℝ) : ℂ) * Complex.I)‖ := by
  obtain ⟨h,hh,hlen,hinj⟩ := uniform_ordinate_grid freq hfreq hL
  let phase (i : Fin m) (j : Fin (m+1)) : ℂ :=
    Complex.exp ((((j.val : ℝ) * h * freq i : ℝ) : ℂ) * Complex.I)
  obtain ⟨δ,hδ,hgap⟩ := finite_ordinate_separation phase hinj
  refine ⟨δ,hδ,?_⟩
  intro a z hz
  let u (i : Fin m) : ℂ := z i * Complex.exp (((-(a+L) * freq i : ℝ) : ℂ) * Complex.I)
  have hu (i : Fin m) : ‖u i‖ = 1 := by simp [u, hz i, Complex.norm_exp]
  obtain ⟨j, hj⟩ := finite_grid_euler_factor_separation
    (V := Fin m) (J := Fin (m+1)) (by simp) (fun i j => u i * phase i j) δ
    (by intro i j k hjk; rw [← mul_sub, norm_mul, hu, one_mul]; exact hgap i j k hjk)
  refine ⟨a+L - (j.val : ℝ)*h, ?_, ?_⟩
  · have hjm : (j.val : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
    constructor
    · linarith [mul_le_mul_of_nonneg_right hjm hh.le]
    · have hj0 : 0 ≤ (j.val : ℝ)*h := by positivity
      linarith
  intro i
  have hp : u i * phase i j = z i * Complex.exp
      (((-(a+L - (j.val : ℝ)*h) * freq i : ℝ) : ℂ) * Complex.I) := by
    dsimp [u,phase]
    rw [mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  simpa only [hp] using hj i


theorem solution {m : ℕ} (q : Fin m → ℝ) (hq : ∀ i, 1 < q i) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : Fin m → ℂ, (∀ i, ‖z i‖ = 1) →
      ∃ T : ℤ → ℝ, (∀ k : ℤ, T k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) ∧
        (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
        (∀ k, T k ≤ T (k+1)) ∧
        Filter.Tendsto (fun k => |T k|) Filter.cofinite Filter.atTop ∧
        ∀ k (σ : ℝ), c ≤ ∏ i, ‖1 - z i * (q i : ℂ) ^ (-((σ : ℂ) + (T k : ℂ) * Complex.I))‖ := by
  obtain ⟨δ,hδ,hgrid⟩ := ordinate_in_every_interval (fun i => Real.log (q i))
    (fun i => Real.log_pos (hq i)) (L := 1) zero_lt_one
  refine ⟨(δ / 2)^m, by positivity, ?_⟩
  intro z hz
  apply good_ordinates_of_unit_intervals (fun t => ∀ σ : ℝ,
    (δ/2)^m ≤ ∏ i, ‖1 - z i * (q i : ℂ) ^ (-((σ : ℂ) + (t : ℂ)*Complex.I))‖)
  intro k
  obtain ⟨t,ht,hfactor⟩ := hgrid k z hz
  refine ⟨t,ht.1,ht.2,?_⟩
  intro σ
  have hprod := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin m)))
    (f := fun _ => δ / 2)
    (g := fun i => ‖1 - z i * (q i : ℂ) ^ (-((σ : ℂ) + (t : ℂ)*Complex.I))‖)
    (fun _ _ => by positivity) (by
      intro i _
      have h := euler_factor_cpow_radial_bound (q i) (zero_lt_one.trans (hq i)) t σ (z i) (hz i)
      linarith [hfactor i])
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

