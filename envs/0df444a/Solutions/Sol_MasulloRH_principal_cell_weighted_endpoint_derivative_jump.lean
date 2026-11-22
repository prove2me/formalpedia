-- Prove2me | solution 1 for MasulloRH.principal_cell_weighted_endpoint_derivative_jump
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T20:17:09.027839+00:00
-- url     : https://prove2.me/submissions/d071c125-c757-4f48-b0a2-64eb4fd12689

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Filter Set
open scoped Topology

private theorem endpoint_floor_local (L : ℝ) (hL : 0 < L) (A : ℕ → ℝ) :
    LocallyIntegrable (fun x : ℝ => A ⌊x/L⌋₊) volume := by
  let M (n : ℕ) := ∑ k ∈ Finset.range (n+1), ‖A k‖
  have hm : Monotone M := by
    apply monotone_nat_of_le_succ
    intro n
    change M n ≤ M (n+1)
    calc
      M n ≤ M n+‖A (n+1)‖ := le_add_of_nonneg_right (norm_nonneg _)
      _ = M (n+1) := (Finset.sum_range_succ _ _).symm
  have hfloor : Monotone (fun x : ℝ => ⌊x / L⌋₊) :=
    fun _ _ h => Nat.floor_mono (div_le_div_of_nonneg_right h hL.le)
  apply ((hm.comp hfloor).locallyIntegrable (μ := volume)).mono
  · exact ((measurable_of_countable A).comp (by fun_prop)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro x
    change ‖A ⌊x/L⌋₊‖ ≤ ‖M ⌊x/L⌋₊‖
    have hM (n : ℕ) : 0 ≤ M n := by dsimp [M]; positivity
    rw [Real.norm_of_nonneg (hM _)]
    exact Finset.single_le_sum (f := fun k => ‖A k‖) (fun k _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self _))

private theorem endpoint_atom_step (q : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), q^(n-k)*w k) =
      q*(∑ k ∈ Finset.range n, q^(n-1-k)*w k) + w n := by
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have h : n-k = (n-1-k)+1 := by have := Finset.mem_range.mp hk; omega
  rw [h, pow_succ]
  ring

open Set Filter MeasureTheory
open scoped Topology Interval

private theorem endpoint_jump_ftc_left {D : ℝ → ℝ} {c v : ℝ}
    (hD : LocallyIntegrable D volume) (hv : Tendsto D (𝓝[<] c) (𝓝 v)) :
    HasDerivWithinAt (fun R => ∫ t in 0..R, D t) v (Iic c) c := by
  have hInt : IntervalIntegrable D volume 0 c :=
    intervalIntegrable_iff.mpr ((hD.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self)
  apply intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right
    (t := Iic c) hInt hD.aestronglyMeasurable.stronglyMeasurableAtFilter
  apply hv.mono_left
  change (𝓝[≤] c ⊓ ae volume) ≤ 𝓝 c ⊓ 𝓟 (Iio c)
  refine le_inf (inf_le_left.trans nhdsWithin_le_nhds) (le_principal_iff.mpr ?_)
  have hle : ∀ᶠ t : ℝ in 𝓝[≤] c ⊓ ae volume, t ≤ c :=
    Filter.Eventually.filter_mono inf_le_left (show ∀ᶠ t : ℝ in 𝓝[≤] c, t ≤ c from self_mem_nhdsWithin)
  have hne : ∀ᶠ t : ℝ in 𝓝[≤] c ⊓ ae volume, t ≠ c :=
    Filter.Eventually.filter_mono inf_le_right (show ∀ᶠ t : ℝ in ae volume, t ≠ c from by simp [ae_iff])
  filter_upwards [hle, hne] with t ht h
  exact lt_of_le_of_ne ht h

private theorem endpoint_jump_ftc_right {D : ℝ → ℝ} {c v : ℝ}
    (hD : LocallyIntegrable D volume) (hv : Tendsto D (𝓝[>] c) (𝓝 v)) :
    HasDerivWithinAt (fun R => ∫ t in 0..R, D t) v (Ici c) c := by
  have hInt : IntervalIntegrable D volume 0 c :=
    intervalIntegrable_iff.mpr ((hD.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self)
  exact intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right
    (t := Ioi c) hInt hD.aestronglyMeasurable.stronglyMeasurableAtFilter (hv.mono_left inf_le_left)

theorem solution (L α b : ℝ) (hL : 0 < L) (hα : 0 < α)
    (f : ℝ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (n : ℕ) :
    let r := Real.exp (-α*L)
    let cell := fun (m : ℕ) (x : ℝ) => -Real.sqrt (2*α) *
      Real.exp (-α*x+α*(2*(x-L*(m:ℝ))-L))
    let g := fun x : ℝ => if 0 ≤ x then cell ⌊x/L⌋₊ x else 0
    let V := fun x : ℝ => ∫ t : ℝ, g t * (Real.exp (-b*(x-t))*f (x-t))
    let A := fun m : ℕ => (1-r^2) * ∑ k ∈ Finset.range m,
      (r^2)^(m-1-k) * (Real.exp (-((k:ℝ)+1)*L/2) * f (((k:ℝ)+1)*L))
    let d := fun x : ℝ => A ⌊x/L⌋₊ - g x * V x
    let x₀ := ((n:ℝ)+1)*L
    let dLeft := A n - cell n x₀ * V x₀
    let dRight := A (n+1) - cell (n+1) x₀ * V x₀
    Continuous V ∧ LocallyIntegrable d volume ∧
    Tendsto d (𝓝[<] x₀) (𝓝 dLeft) ∧ Tendsto d (𝓝[>] x₀) (𝓝 dRight) ∧
    HasDerivWithinAt (fun R => ∫ t in 0..R, d t) dLeft (Iic x₀) x₀ ∧
    HasDerivWithinAt (fun R => ∫ t in 0..R, d t) dRight (Ici x₀) x₀ ∧
    dRight - r^2*dLeft = (1-r^2)*Real.exp (-x₀/2)*f x₀ := by
  dsimp only
  let r := Real.exp (-α*L)
  let cell (m : ℕ) (x : ℝ) := -Real.sqrt (2*α) *
    Real.exp (-α*x+α*(2*(x-L*(m:ℝ))-L))
  let g (x : ℝ) := if 0 ≤ x then cell ⌊x/L⌋₊ x else 0
  let F (s : ℝ) := Real.exp (-b*s)*f s
  let V (x : ℝ) := ∫ t : ℝ, g t * F (x-t)
  let w (k : ℕ) := Real.exp (-((k:ℝ)+1)*L/2)*f (((k:ℝ)+1)*L)
  let A (m : ℕ) := (1-r^2) * ∑ k ∈ Finset.range m, (r^2)^(m-1-k)*w k
  let d (x : ℝ) := A ⌊x/L⌋₊ - g x * V x
  let x₀ := ((n:ℝ)+1)*L
  let K := Real.sqrt (2*α)*Real.exp (α*L)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hgm : Measurable g := by
    apply Measurable.ite (p := fun t : ℝ => 0 ≤ t) measurableSet_Ici _ measurable_const
    dsimp [cell]; fun_prop
  have hgb (x : ℝ) : ‖g x‖ ≤ K := by
    by_cases hx : 0 ≤ x
    · have hfloor : x < L * ((⌊x/L⌋₊:ℝ)+1) := by
        have hh := Nat.lt_floor_add_one (x/L)
        calc
          x < ((⌊x/L⌋₊:ℝ)+1) * L := (div_lt_iff₀ hL).mp hh
          _ = _ := mul_comm _ _
      simp only [g, if_pos hx, cell, norm_mul, norm_neg, Real.norm_of_nonneg
        (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.exp_pos _).le]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply Real.exp_le_exp.mpr
      have hθ : x - L * (⌊x/L⌋₊:ℝ) ≤ L := by linarith
      have h1 := mul_le_mul_of_nonneg_left hθ hα.le
      have h2 := mul_nonneg hα.le hx
      linarith
    · simpa [g, hx] using hK
  have hgi : LocallyIntegrable g volume := by
    apply (continuous_const (y := K)).locallyIntegrable.mono hgm.aestronglyMeasurable
    filter_upwards with x
    simpa [Real.norm_of_nonneg hK] using hgb x
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hFc : HasCompactSupport F := hfc.mul_left
  have hV : Continuous V :=
    hFc.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hgi hF
  have hprod : LocallyIntegrable (fun x => g x * V x) volume := by
    have hmaj : Continuous (fun x => K*‖V x‖) := continuous_const.mul hV.norm
    apply hmaj.locallyIntegrable.mono (hgm.mul hV.measurable).aestronglyMeasurable
    filter_upwards with x
    change ‖g x * V x‖ ≤ ‖K*‖V x‖‖
    rw [norm_mul, Real.norm_of_nonneg (mul_nonneg hK (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hgb x) (norm_nonneg _)
  have hd : LocallyIntegrable d volume := (endpoint_floor_local L hL A).sub hprod
  have hcell (m : ℕ) {x : ℝ} (hx : x ∈ Ioo ((m:ℝ)*L) (((m:ℝ)+1)*L)) :
      ⌊x/L⌋₊ = m ∧ g x = cell m x := by
    have he : ⌊x/L⌋₊ = m := (Nat.floor_eq_iff (show 0 ≤ x / L from div_nonneg ((mul_nonneg (Nat.cast_nonneg _) hL.le).trans hx.1.le) hL.le)).mpr (by
      constructor
      · exact (le_div_iff₀ hL).mpr hx.1.le
      · exact (div_lt_iff₀ hL).mpr hx.2)
    exact ⟨he, by simp [g, he, show 0 ≤ x from (mul_nonneg (Nat.cast_nonneg _) hL.le).trans hx.1.le]⟩
  have hcts (m : ℕ) : Continuous (fun x : ℝ => A m - cell m x*V x) := by
    dsimp [cell]; fun_prop
  have hl : Tendsto d (𝓝[<] x₀) (𝓝 (A n-cell n x₀*V x₀)) := by
    apply ((hcts n).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [Ioo_mem_nhdsLT (show (n:ℝ)*L < x₀ by dsimp [x₀]; linarith)] with x hx
    obtain ⟨h1,h2⟩ := hcell n hx
    dsimp only [d]; rw [h1,h2]
  have hr : Tendsto d (𝓝[>] x₀) (𝓝 (A (n+1)-cell (n+1) x₀*V x₀)) := by
    apply ((hcts (n+1)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    have hx' : x₀ = ((n+1:ℕ):ℝ)*L := by simp [x₀]
    filter_upwards [Ioo_mem_nhdsGT (show x₀ < (((n+1:ℕ):ℝ)+1)*L by rw [hx']; linarith)] with x hx
    rw [hx'] at hx
    obtain ⟨h1,h2⟩ := hcell (n+1) hx
    dsimp only [d]; rw [h1,h2]
  have hgstep : cell (n+1) x₀ = r^2*cell n x₀ := by
    dsimp [cell, r, x₀]; push_cast
    rw [sq, ← Real.exp_add, mul_left_comm _ (-Real.sqrt _), ← Real.exp_add]
    congr 2
    ring
  have hstep : A (n+1) = r^2*A n + (1-r^2)*w n := by
    dsimp only [A]
    rw [Nat.add_sub_cancel, endpoint_atom_step]
    ring
  refine ⟨hV, hd, hl, hr, endpoint_jump_ftc_left hd hl, endpoint_jump_ftc_right hd hr, ?_⟩
  change A (n+1)-cell (n+1) x₀ * V x₀-r^2*(A n-cell n x₀*V x₀) = _
  rw [hstep, hgstep]
  dsimp only [w, x₀, r]
  ring_nf

#print axioms solution
