-- Prove2me | solution 1 for MasulloRH.prime_halfspace_relative_diagonal_mass
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:08:51.655626+00:00
-- url     : https://prove2.me/submissions/f2b5d2d5-325d-47d2-8b90-97fd6997cc88

import Theorems.Thm_MasulloRH_bilateral_scattering_coefficients
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
open Set MeasureTheory

private noncomputable def slab (a b x : ℝ) := (if x ≤ b then (1:ℝ) else 0) - (if x ≤ a then (1:ℝ) else 0)

private theorem slab_pos {a b : ℝ} (hab : a ≤ b) :
    slab a b = (Ioc a b).indicator (fun _ => (1:ℝ)) := by
  funext x
  simp only [slab,Set.indicator_apply,mem_Ioc]
  split_ifs <;> simp_all <;> linarith

private theorem slab_norm_and_int (a b : ℝ) :
    Integrable (slab a b) ∧ (∫ x, slab a b x) = b-a ∧ (∫ x, |slab a b x|) = |b-a| := by
  have f {a b : ℝ} (h : a ≤ b) : Integrable (slab a b) ∧ (∫ x, slab a b x) = b-a ∧
      (∀ x, 0 ≤ slab a b x) := by
    rw [slab_pos h]
    exact ⟨(integrableOn_const (C := (1:ℝ)) measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc,
      by rw [integral_indicator_const _ measurableSet_Ioc,Real.volume_real_Ioc,smul_eq_mul,mul_one,max_eq_left (sub_nonneg.mpr h)], fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x⟩
  rcases le_total a b with h | h
  · obtain ⟨hi,he,hp⟩ := f h
    exact ⟨hi,he,by simp only [abs_of_nonneg (hp _),abs_of_nonneg (sub_nonneg.mpr h)]; exact he⟩
  · have neg : slab a b = fun x => -slab b a x := by funext x; simp [slab]
    obtain ⟨hi,he,hp⟩ := f h
    rw [neg]
    exact ⟨hi.neg,by rw [integral_neg,he]; ring, by simp only [abs_neg,abs_of_nonneg (hp _), abs_of_nonpos (sub_nonpos.mpr h),neg_sub]; exact he⟩

theorem MasulloRH.halfspace_shift_boundary_integral (L : ℝ) (hL : 0 ≤ L) (d : ℤ)
    (b : ℤ → ℝ) (s : ℝ) (hs : HasSum (fun j : ℤ => (j:ℝ)*b (j-d)*b j) s) :
    let K (j : ℤ) (u : ℝ) := (b (j-d)*b j) *
      ((if u ≤ ((j:ℝ)-(d:ℝ))*L then (1:ℝ) else 0) - (if u ≤ -(d:ℝ)*L then 1 else 0))
    Summable (fun j => ∫ u, |K j u|) ∧ (∫ u, ∑' j, K j u) = L*s := by
  intro K
  let a := -(d:ℝ)*L
  let z (j : ℤ) := ((j:ℝ)-(d:ℝ))*L
  have hdiff (j : ℤ) : z j-a=(j:ℝ)*L := by dsimp [z,a]; ring
  have hi j : Integrable (K j) := (slab_norm_and_int a (z j)).1.const_mul _
  have hz j : (∫ u, K j u) = ((j:ℝ)*b (j-d)*b j)*L := by
    change (∫ u, (b (j-d)*b j)*slab a (z j) u) = _
    rw [integral_const_mul,(slab_norm_and_int a _).2.1,hdiff]; ring
  have hnorm j : (∫ u, |K j u|) = |((j:ℝ)*b (j-d)*b j)| * L := by
    change (∫ u, |(b (j-d)*b j)*slab a (z j) u|) = _
    simp_rw [abs_mul]
    rw [integral_const_mul,(slab_norm_and_int a _).2.2,hdiff,abs_mul,abs_of_nonneg hL]; ring
  have hsum : Summable (fun j => ∫ u, |K j u|) := by
    simp_rw [hnorm]; exact hs.summable.abs.mul_right _
  refine ⟨hsum, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hi (by simpa only [Real.norm_eq_abs] using hsum)]
  simp_rw [hz]; rw [tsum_mul_right,hs.tsum_eq,mul_comm]
open Set MeasureTheory Finset
theorem solution (p : ℕ) (hp : p.Prime) (T : Finset ℤ) (f : ℝ → ℂ) :
    let L := Real.log p
    let r := 1/Real.sqrt p
    let b (j : ℤ) : ℝ := if j = -1 then -r else if 0 ≤ j then (1-r^2)*r^j.toNat else 0
    let K (d j : ℤ) (u : ℝ) := (b (j-d)*b j) *
      ((if u ≤ ((j:ℝ)-(d:ℝ))*L then (1:ℝ) else 0) - (if u ≤ -(d:ℝ)*L then 1 else 0))
    (∀ d, Summable (fun j => ∫ u : ℝ, |K d j u|)) ∧
    (∑ d ∈ T, (Complex.ofReal (∫ u : ℝ, ∑' j : ℤ, K d j u)) * f ((d:ℝ)*L)) =
      (L:ℂ) * ∑ d ∈ T, (if d=0 then 0 else (r^d.natAbs:ℝ):ℂ) * f ((d:ℝ)*L) := by
  intro L r b K
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hL : 0 ≤ L := (Real.log_pos hp1).le
  have hr₁ : 1 < Real.sqrt (p : ℝ) := by nlinarith [Real.sq_sqrt (show 0 ≤ (p:ℝ) by positivity),Real.sqrt_nonneg (p:ℝ)]
  have hr : 0 < r := one_div_pos.mpr (by linarith)
  have hlt : r < 1 := (div_lt_iff₀ (by linarith : 0 < Real.sqrt (p:ℝ))).2 (by linarith)
  have H (d : ℤ) := MasulloRH.halfspace_shift_boundary_integral L hL d b _ (((MasulloRH.bilateral_scattering_coefficients r hr hlt).1 d).2)
  refine ⟨fun d => (H d).1, ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [show (∫ u : ℝ, ∑' j : ℤ, K d j u) = _ from (H d).2]
  push_cast
  split_ifs <;> push_cast <;> ring
