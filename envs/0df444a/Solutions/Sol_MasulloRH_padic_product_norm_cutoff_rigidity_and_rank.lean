-- Prove2me | solution 1 for MasulloRH.padic_product_norm_cutoff_rigidity_and_rank
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:41:59.55832+00:00
-- url     : https://prove2.me/submissions/e6551ad1-81cd-49bc-a0ac-5a16f43c5de9

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.Basic
section

open Set Filter
open scoped Topology

namespace MasulloRH

/-- A neighborhood of zero contains a nonzero element of the valuation unit ball. -/
theorem small_nonzero_mem_nhds_zero {K : Type*} [NontriviallyNormedField K] {U : Set K}
    (hU : U ∈ 𝓝 (0 : K)) : ∃ y ∈ U, y ≠ 0 ∧ ‖y‖ ≤ 1 := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨y,hy,hyr⟩ := NormedField.exists_norm_lt K (lt_min hr zero_lt_one)
  have hy' : ‖y‖ < r := lt_of_lt_of_le hyr (min_le_left _ _)
  exact ⟨y,hrU (by simpa only [Metric.mem_ball, dist_zero_right] using hy'),
    norm_pos_iff.mp hy, (hyr.le.trans (min_le_right _ _))⟩

theorem padic_small_nonzero_mem_nhds_zero (p : ℕ) [Fact p.Prime] {U : Set ℚ_[p]}
    (hU : U ∈ 𝓝 (0 : ℚ_[p])) : ∃ y ∈ U, y ≠ 0 ∧ ‖y‖ ≤ 1 :=
  small_nonzero_mem_nhds_zero hU

theorem padic_open_addSubgroup_has_small_nonzero (p : ℕ) [Fact p.Prime]
    (H : AddSubgroup ℚ_[p]) (hH : IsOpen (H : Set ℚ_[p])) :
    ∃ y ∈ H, y ≠ 0 ∧ ‖y‖ ≤ 1 :=
  small_nonzero_mem_nhds_zero (hH.mem_nhds H.zero_mem)

end MasulloRH
end

section

open Finset

namespace MasulloRH

/-- A product-of-norms cutoff has infinite tensor rank even on the second unit ball,
provided the unrestricted positive real profile never vanishes. -/
theorem product_window_no_finite_separated_representation (K : Type*) [NontriviallyNormedField K]
    (w : ℝ → ℂ) (m : ℝ → ℂ) {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hw : ∀ x : ℝ, 0 < x → w x ≠ 0) (hm : m a ≠ 0) (htail : ∀ t : ℝ, C ≤ t → m t = 0) :
    ¬ ∃ (d : ℕ) (A : Fin d → ℝ → ℂ) (B : Fin d → K → ℂ),
      ∀ x : ℝ, 0 < x → ∀ y : K, ‖y‖ ≤ 1 →
        w x * m (|x| * ‖y‖) = ∑ k : Fin d, A k x * B k y := by
  rintro ⟨d,A,B,hAB⟩
  obtain ⟨y,hy,hy'⟩ := NormedField.exists_norm_lt K (lt_min zero_lt_one (div_pos ha hC))
  let q := ‖y‖
  have hq : 0 < q := hy
  have hq1 : q ≤ 1 := (lt_of_lt_of_le hy' (min_le_left _ _)).le
  have hCa : C * q ≤ a := by
    have hh := (lt_div_iff₀ hC).mp (lt_of_lt_of_le hy' (min_le_right _ _))
    exact (mul_comm C q) ▸ hh.le
  let x (i : Fin (d+1)) := a/q^i.val
  have hx (i : Fin (d+1)) : 0 < x i := div_pos ha (pow_pos hq _)
  let M : Matrix (Fin (d+1)) (Fin (d+1)) ℂ := fun i j => w (x i) * m (x i*q^j.val)
  have htri : M.IsUpperTriangular := by
    intro i j hij
    change w (x i) * m (x i*q^j.val) = 0
    rw [htail, mul_zero]
    have hpow : q^i.val ≤ q^(j.val+1) := pow_le_pow_of_le_one hq.le hq1 (show j.val+1 ≤ i.val from hij)
    have hbound : C*q^i.val ≤ a*q^j.val := calc
      _ ≤ C * q^(j.val+1) := mul_le_mul_of_nonneg_left hpow hC.le
      _ = C*q*q^j.val := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCa (pow_nonneg hq.le _)
    change C ≤ a / q^i.val * q^j.val
    rwa [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hq _)]
  have hdiag (i : Fin (d+1)) : M i i ≠ 0 := by
    change w (x i) * m (a/q^i.val*q^i.val) ≠ 0
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hq.ne')]
    exact mul_ne_zero (hw _ (hx i)) hm
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)
  let U : Matrix (Fin (d+1)) (Fin d) ℂ := fun i k => A k (x i)
  let V : Matrix (Fin d) (Fin (d+1)) ℂ := fun k j => B k (y^j.val)
  have hf : M = U*V := by
    ext i j
    have hj : ‖y^j.val‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ hq.le hq1
    rw [Matrix.mul_apply]
    simpa only [M,U,V,abs_of_pos (hx i), norm_pow, q] using
      hAB (x i) (hx i) (y^j.val) hj
  have ht : M.rank = d+1 := by simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hdet
  have hle : M.rank ≤ d := hf ▸ (Matrix.rank_mul_le_left U V).trans U.rank_le_width
  omega

/-- In particular, arbitrary p-adic factors cannot represent the upper norm window times a Gaussian. -/
theorem padic_gaussian_upper_window_infinite_rank (p : ℕ) [Fact p.Prime] (m : ℝ → ℂ)
    {a C : ℝ} (ha : 0 < a) (hC : 0 < C) (hm : m a ≠ 0)
    (htail : ∀ t : ℝ, C ≤ t → m t = 0) :
    ¬ ∃ (d : ℕ) (A : Fin d → ℝ → ℂ) (B : Fin d → ℚ_[p] → ℂ),
      ∀ x : ℝ, 0 < x → ∀ y : ℚ_[p], ‖y‖ ≤ 1 →
        (Real.exp (-x^2) : ℂ) * m (|x| * ‖y‖) = ∑ k : Fin d, A k x * B k y := by
  exact product_window_no_finite_separated_representation ℚ_[p] _ m ha hC
    (fun x _ => Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') hm htail

end MasulloRH
end

section

open Filter Set
open scoped Topology
namespace MasulloRH

private noncomputable def radialQp (p : ℕ) [Fact p.Prime]
    (m : ℝ → ℝ) (x : ℝ) (y : ℚ_[p]) : ℂ :=
  if ‖y‖ ≤ 1 then (Real.exp (-(x^2)) : ℂ) * (m (|x| *‖y‖):ℂ) else 0

private theorem radialQp_iff (p : ℕ) [Fact p.Prime] (m : ℝ → ℝ) :
    (∀ᶠ y in 𝓝 (0:ℚ_[p]), ∀ x : ℝ, radialQp p m x y = radialQp p m x 0) ↔
      ∀ t : ℝ, 0 ≤ t → m t = m 0 := by
  constructor
  · intro H t ht
    obtain ⟨y,hy,hy0,hy1⟩ := MasulloRH.padic_small_nonzero_mem_nhds_zero p H
    let x := t/‖y‖
    have h₁ : 0 ≤ x := div_nonneg ht (norm_nonneg _)
    have h₂ : |x| *‖y‖ = t := by rw [abs_of_nonneg h₁]; exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy0)
    have hh : radialQp p m x y = radialQp p m x 0 := hy x
    simp only [radialQp, if_pos hy1, h₂, norm_zero, zero_le_one, if_true, mul_zero] at hh
    apply Complex.ofReal_injective
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hh
  · intro hm
    filter_upwards [Metric.ball_mem_nhds (0:ℚ_[p]) (by norm_num : (0:ℝ)<1)] with y hy x
    have hyn : ‖y‖≤1 := (show ‖y‖ < 1 by simpa only [Metric.mem_ball,dist_zero_right] using hy).le
    simp [radialQp,hyn,hm _ (mul_nonneg (abs_nonneg _) (norm_nonneg _))]

private theorem radialQp_const_of_tensor (p : ℕ) [Fact p.Prime] (m : ℝ → ℝ)
    (hn : ∃ (n : ℕ) (a : Fin n → ℝ → ℂ) (b : Fin n → ℚ_[p] → ℂ),
      (∀ i, IsLocallyConstant (b i)) ∧
        ∀ x y, radialQp p m x y = ∑ i, a i x * b i y) :
    ∀ t : ℝ, 0 ≤ t → m t = m 0 := by
  obtain ⟨n,a,b,hb,he⟩ := hn
  apply (radialQp_iff p m).mp
  have hlocal : ∀ᶠ y in 𝓝 (0:ℚ_[p]), ∀ i, b i y = b i 0 :=
    eventually_all.mpr fun i => (hb i).eventually_eq 0
  filter_upwards [hlocal] with y hy x
  simp only [he,hy]

private theorem radialQp_const_of_period (p : ℕ) [Fact p.Prime] (m : ℝ → ℝ)
    (hn : ∃ H : AddSubgroup ℚ_[p], IsOpen (H : Set ℚ_[p]) ∧
      ∀ (x : ℝ) (y : ℚ_[p]) (h : ℚ_[p]), h ∈ H → radialQp p m x (y+h) = radialQp p m x y) :
    ∀ t : ℝ, 0 ≤ t → m t = m 0 := by
  obtain ⟨H,ho,hp⟩ := hn
  apply (radialQp_iff p m).mp
  filter_upwards [ho.mem_nhds H.zero_mem] with h hh x
  simpa only [zero_add] using hp x 0 h hh

private theorem radialQp_no_finite_rank (p : ℕ) [Fact p.Prime] (m : ℝ → ℝ)
    {a C : ℝ} (ha : 0 < a) (hC : 0 < C) (hm : m a ≠ 0) (hcut : ∀ t : ℝ, C≤t → m t=0) :
    ¬ ∃ (n : ℕ) (A : Fin n → ℝ → ℂ) (B : Fin n → ℚ_[p] → ℂ),
      ∀ x : ℝ, 0<x → ∀ y : ℚ_[p], ‖y‖≤1 → radialQp p m x y = ∑ k, A k x * B k y := by
  intro he
  apply padic_gaussian_upper_window_infinite_rank p (fun t => (m t:ℂ)) ha hC
    (Complex.ofReal_ne_zero.mpr hm) (fun t ht => by simp [hcut t ht])
  obtain ⟨n,A,B,h⟩ := he
  exact ⟨n,A,B,fun x hx y hy => by simpa only [radialQp,if_pos hy] using h x hx y hy⟩

end MasulloRH
end

section

theorem MasulloRH.bounded_real_window_product_cutoff_period (p : ℕ) [Fact p.Prime]
    (m : ℝ → ℝ) (X δ d : ℝ) (hX : 0 < X) (_hδ : 0 < δ)
    (hflat : ∀ t : ℝ, 0 ≤ t → t ≤ δ → m t = m 0)
    (f : ℝ → ℚ_[p] → ℂ) (hf : ∀ x, X < |x| → ∀ y, f x y = 0)
    (hper : ∀ x y h, ‖h‖ ≤ d → f x (y+h) = f x y) :
    ∀ (x : ℝ) (y h : ℚ_[p]), ‖h‖ ≤ min d (δ/X) →
      (m (|x| * ‖y+h‖) : ℂ)*f x (y+h) = (m (|x| * ‖y‖) : ℂ)*f x y := by
  intro x y h hh
  rw [hper x y h (hh.trans (min_le_left _ _))]
  by_cases hx : X < |x|
  · simp [hf x hx y]
  have hn : ‖h‖ ≤ δ/X := hh.trans (min_le_right _ _)
  by_cases hy : ‖y‖ ≤ δ/X
  · have bound {t : ℝ} (ht : 0 ≤ t) (hu : t ≤ δ/X) : m (|x| * t) = m 0 := by
      apply hflat _ (mul_nonneg (abs_nonneg _) ht)
      calc
        |x| * t ≤ X*t := mul_le_mul_of_nonneg_right (le_of_not_gt hx) ht
        _ ≤ δ := by rw [mul_comm]; exact (le_div_iff₀ hX).mp hu
    rw [bound (norm_nonneg _) ((Padic.nonarchimedean y h).trans (max_le hy hn)),
        bound (norm_nonneg _) hy]
  · have hlt : ‖h‖ < ‖y‖ := lt_of_le_of_lt hn (lt_of_not_ge hy)
    rw [Padic.add_eq_max_of_ne hlt.ne', max_eq_left hlt.le]
end

section
open Filter Set
open scoped Topology

theorem solution (p : ℕ) [Fact p.Prime] :
    let F (m : ℝ → ℝ) (x : ℝ) (y : ℚ_[p]) : ℂ :=
      if ‖y‖ ≤ 1 then (Real.exp (-(x^2)):ℂ) * (m (|x| * ‖y‖):ℂ) else 0
    let UniformAtZero (m : ℝ → ℝ) := ∀ᶠ y in 𝓝 (0:ℚ_[p]), ∀ x : ℝ, F m x y = F m x 0
    let CommonPeriod (m : ℝ → ℝ) := ∃ H : AddSubgroup ℚ_[p], IsOpen (H : Set ℚ_[p]) ∧
      ∀ (x : ℝ) (y h : ℚ_[p]), h ∈ H → F m x (y+h) = F m x y
    let FiniteLoc (m : ℝ → ℝ) := ∃ (n : ℕ) (a : Fin n → ℝ → ℂ) (b : Fin n → ℚ_[p] → ℂ),
      (∀ i, IsLocallyConstant (b i)) ∧ ∀ x y, F m x y = ∑ i, a i x * b i y
    let FiniteOnBall (m : ℝ → ℝ) := ∃ (n : ℕ) (a : Fin n → ℝ → ℂ) (b : Fin n → ℚ_[p] → ℂ),
      ∀ x : ℝ, 0<x → ∀ y : ℚ_[p], ‖y‖≤1 → F m x y = ∑ i, a i x * b i y
    (∀ m : ℝ → ℝ, (UniformAtZero m ↔ ∀ t : ℝ, 0 ≤ t → m t = m 0) ∧
      (CommonPeriod m → ∀ t : ℝ, 0 ≤ t → m t = m 0) ∧
      (FiniteLoc m → ∀ t : ℝ, 0 ≤ t → m t = m 0) ∧
      (∀ a C : ℝ, 0<a → 0<C → m a ≠ 0 → (∀ t : ℝ, C≤t → m t=0) → ¬FiniteOnBall m)) ∧
    (∀ (m : ℝ → ℝ) (X δ d : ℝ), 0<X → 0<δ → 0<d →
      (∀ t : ℝ, 0 ≤ t → t ≤ δ → m t = m 0) →
      ∀ f : ℝ → ℚ_[p] → ℂ, (∀ x, X < |x| → ∀ y, f x y = 0) →
      (∀ x y h, ‖h‖ ≤ d → f x (y+h) = f x y) →
      ∀ (x : ℝ) (y h : ℚ_[p]), ‖h‖ ≤ min d (δ/X) →
        (m (|x| * ‖y+h‖):ℂ) * f x (y+h) = (m (|x| * ‖y‖):ℂ) * f x y) ∧
    ∃ m : ℝ → ℝ, ContDiff ℝ (⊤:ℕ∞) m ∧ HasCompactSupport m ∧
      (∀ t, 0 ≤ m t ∧ m t ≤ 1) ∧ (∀ t : ℝ, |t| ≤ 1 → m t = 1) ∧
      (∀ t : ℝ, 2 ≤ |t| → m t = 0) ∧
      ¬UniformAtZero m ∧ ¬CommonPeriod m ∧ ¬FiniteLoc m ∧ ¬FiniteOnBall m := by
  dsimp only
  constructor
  · intro m
    exact ⟨MasulloRH.radialQp_iff p m, MasulloRH.radialQp_const_of_period p m,
      MasulloRH.radialQp_const_of_tensor p m, fun _ _ ha hC hm ht => MasulloRH.radialQp_no_finite_rank p m ha hC hm ht⟩
  constructor
  · intro m X δ d hX hδ _ hflat f hf hper
    exact MasulloRH.bounded_real_window_product_cutoff_period p m X δ d hX hδ hflat f hf hper
  · let b : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
    have hb1 (t : ℝ) (ht : |t|≤1) : b t = 1 := by
      apply b.one_of_mem_closedBall
      simpa [Metric.mem_closedBall,Real.dist_eq,b] using ht
    have hb2 (t : ℝ) (ht : 2≤|t|) : b t = 0 := by
      apply b.zero_of_le_dist
      simpa [Real.dist_eq,b] using ht
    have hnot (H : ∀ t : ℝ, 0 ≤ t → b t = b 0) : False := by
      have h := H 2 (by norm_num)
      rw [hb2 _ (by norm_num),hb1 _ (by norm_num)] at h
      norm_num at h
    have hnonzero : b 1 ≠ 0 := by rw [hb1 1 (by norm_num)]; exact one_ne_zero
    exact ⟨b,b.contDiff,b.hasCompactSupport,fun t => ⟨b.nonneg,b.le_one⟩,hb1,hb2,
      fun h => hnot ((MasulloRH.radialQp_iff p b).mp h),
      fun h => hnot (MasulloRH.radialQp_const_of_period p b h),
      fun h => hnot (MasulloRH.radialQp_const_of_tensor p b h),
      MasulloRH.radialQp_no_finite_rank p b (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<2)
        hnonzero (fun t ht => hb2 t (ht.trans (le_abs_self _)))⟩
end
