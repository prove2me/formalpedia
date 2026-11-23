-- Prove2me | solution 1 for NoHair.static_negative_sheet_pole_from_lapse_monopole
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:54:13.626289+00:00
-- url     : https://prove2.me/submissions/ea4c6c5c-655f-41ae-9701-0252b7b6a8c8

import Definitions.Def_NoHair_staticInvertedEndMetric

noncomputable section
open NoHair Set Filter
open scoped Topology ContDiff RealInnerProductSpace

private abbrev X := ADMPoint
private abbrev K := Fin 3
private abbrev Mat := Matrix K K ℝ
private abbrev e (i : K) : X := EuclideanSpace.single i 1

private lemma flat_pair (v w : X) :
    (∑ i : K, ∑ j : K, (1:Mat) i j*v i*w j)=inner ℝ v w := by
  simp [Matrix.one_apply,ite_mul,PiLp.inner_apply,Real.inner_apply,mul_comm]

private lemma three_limits {l : Filter X} {f : X → K → ℝ}
    (hf : ∀ k, Tendsto (fun y => f y k) l (𝓝 0)) :
    Tendsto (fun y => ∑ k,f y k) l (𝓝 0) := by
  simpa only [Fin.sum_univ_three,zero_add] using ((hf 0).add (hf 1)).add (hf 2)

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) (μ : ℝ) (hμ : HasStaticLapseMonopole N μ) :
    HasContinuousStaticPole N h μ := by
  let I := EuclideanGeometry.inversion (0:X) 1
  let O := fun y : X => (ℝ ∙ (y-(0:X)))ᗮ.reflection
  let v := fun y k => O y (e k)
  let B := fun y => ‖I y‖*(1-N (I y))/2
  let l := 𝓝[≠] (0:X)
  have nr (y : X) : ‖I y‖=1/‖y‖ := by
    simpa only [dist_zero_right,one_pow] using EuclideanGeometry.dist_inversion_center (0:X) y 1
  have hI : Tendsto I l (Bornology.cobounded X) :=
    EuclideanGeometry.tendsto_inversion_nhdsNE_center_cobounded (by norm_num : (1:ℝ)≠0)
  have hIc : Tendsto I l (cocompact X) := by simpa only [Metric.cobounded_eq_cocompact] using hI
  have hB : Tendsto B l (𝓝 (μ/2)) := (hμ.comp hIc).div_const 2
  have hnorm : Tendsto (fun y => ‖I y‖) l atTop := tendsto_norm_atTop_iff_cobounded.mpr hI
  have nz : ∀ᶠ y in l, y ≠ 0 := self_mem_nhdsWithin
  have small : Tendsto (fun y : X => ‖y‖) l (𝓝 0) := by
    simpa only [norm_zero] using (continuous_norm.continuousAt (x:=(0:X))).tendsto.mono_left nhdsWithin_le_nhds
  have dI {y : X} (hy : y≠0) (i : K) :
      fderiv ℝ I y (e i)=(1/‖y‖)^2 • v y i := by
    have d := (EuclideanGeometry.hasFDerivAt_inversion (R:=1) hy).fderiv
    change fderiv ℝ (EuclideanGeometry.inversion (0:X) 1) y (e i)=_
    rw [d,ContinuousLinearMap.smul_apply,dist_zero_right]
    rfl
  have unit (y : X) (i a : K) : |v y i a| ≤ 1 := by
    calc
      _ ≤ ‖v y i‖ := PiLp.norm_apply_le (v y i) a
      _ = ‖e i‖ := (O y).norm_map _
      _ = 1 := by simp [e]
  have flat (y : X) (i j : K) : (∑ a, ∑ b,(1:Mat) a b*v y i a*v y j b)=(1:Mat) i j := by
    rw [flat_pair,(O y).inner_map_map (e i) (e j)]
    simp [e,EuclideanSpace.inner_single_left,PiLp.single_apply,Matrix.one_apply,eq_comm]
  have factor {y : X} (hy : y ≠ 0) (i j : K) :
      staticInvertedNegativeMetric N h y i j=(B y)^4*(∑ a, ∑ b,h (I y) a b*v y i a*v y j b) := by
    unfold staticInvertedNegativeMetric
    change (∑ a, ∑ b,staticPositiveMetric (fun t => -N t) h (I y) a b*
      (fderiv ℝ I y (e i)) a * (fderiv ℝ I y (e j)) b)=_
    rw [dI hy,dI hy,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [staticPositiveMetric,B,nr,PiLp.smul_apply,smul_eq_mul]
    ring
  obtain ⟨R,C,_,hC,hdecay⟩ := c.falloff 0
  have far : ∀ᶠ y in l, R<‖I y‖ := hnorm.eventually_gt_atTop R
  have limit_err (i j a b : K) : Tendsto (fun y => (h (I y) a b-(1:Mat) a b)*v y i a*v y j b) l (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun y => C*‖y‖)
    · filter_upwards [far,nz] with y hy hy0
      have hg := (hdecay (I y) hy).2 a b
      simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.zero_add,pow_one] at hg
      rw [nr] at hg
      have hab : |h (I y) a b-(1:Mat) a b| ≤ C*‖y‖ := by simpa [div_div_eq_mul_div] using hg
      rw [Real.norm_eq_abs,abs_mul,abs_mul]
      calc
        _ ≤ |h (I y) a b-(1:Mat) a b| * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (unit y i a) (abs_nonneg _)) (unit y j b) (abs_nonneg _) (by positivity)
        _ ≤ _ := by simpa only [mul_one] using hab
    · simpa only [mul_zero] using (tendsto_const_nhds (x:=C)).mul small
  intro i j
  have he := three_limits (f:=fun y a => ∑ b,(h (I y) a b-(1:Mat) a b)*v y i a*v y j b)
    (fun a => three_limits (f:=fun y b => (h (I y) a b-(1:Mat) a b)*v y i a*v y j b) (limit_err i j a))
  have hmetric : Tendsto (fun y => ∑ a,∑ b,h (I y) a b*v y i a*v y j b) l (𝓝 ((1:Mat) i j)) := by
    have hsum := he.add (tendsto_const_nhds (x:=(1:Mat) i j))
    simp only [zero_add] at hsum
    apply hsum.congr'
    filter_upwards with y
    change (∑ a,∑ b,(h (I y) a b-(1:Mat) a b)*v y i a*v y j b)+(1:Mat) i j=_
    rw [← flat y i j]
    simp only [Fin.sum_univ_three]
    ring
  exact ((hB.pow 4).mul hmetric).congr' (nz.mono (fun y hy => (factor hy i j).symm))
