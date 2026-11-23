-- Prove2me | solution 1 for NoHair.positive_static_end_length_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T08:07:32.679669+00:00
-- url     : https://prove2.me/submissions/3ece61d0-e3c5-4159-918a-1796b48d3ffe

import Definitions.Def_NoHair_staticSliceADM

open NoHair Filter Set
open scoped Topology ContDiff Manifold
open Metric MeasureTheory

private abbrev X := ADMPoint

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric c.N c.h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric c.N c.h (γ t) i j * deriv γ t i * deriv γ t j) := by
  classical
  obtain ⟨R₀,C,rp,cp,fall⟩ := c.falloff 0
  obtain ⟨B,hB⟩ := c.compactComplement.isBounded.subset_closedBall (0 : X)
  let R := max R₀ (max B (20*C))
  have rp' : 0 < R := rp.trans_le (le_max_left _ _)
  have cover (x : X) (hx : R < ‖x‖) : x ∈ c.W := by
    apply c.extendsAcross
    apply subset_closure
    by_contra hn
    have h := Metric.mem_closedBall.mp (hB hn)
    have limit := (max_lt_iff.mp (max_lt_iff.mp hx).2).1
    exact limit.not_ge (by simpa only [dist_zero_right] using h)
  have lower (x : X) (hx : R < ‖x‖) (v : X) :
      ‖v‖^2/4 ≤ ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric c.N c.h x i j * v i * v j := by
    have r := rp'.trans hx
    have scale : C / ‖x‖ ≤ 1/20 := (div_le_iff₀ r).mpr (by
      linarith only [(max_lt_iff.mp (max_lt_iff.mp hx).2).2])
    have af := fall x (max_lt_iff.mp hx).1
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.zero_add,pow_one] at af
    have nn : |c.N x-1| ≤ 1/20 := af.1.trans scale
    let w := (1+c.N x)/2
    have wmin : (9/10:ℝ) ≤ w := by dsimp only [w];linarith only [(abs_le.mp nn).1]
    have wlow : (1/2:ℝ) ≤ w^4 :=
      (by norm_num : (1/2:ℝ) ≤ (9/10:ℝ)^4).trans (pow_le_pow_left₀ (by norm_num) wmin 4)
    let δ := (1 : Matrix (Fin 3) (Fin 3) ℝ)
    have vi (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
    have comp (i j : Fin 3) : |(c.h x i j-δ i j)*v i*v j| ≤ (1/20:ℝ)*‖v‖^2 := by
      rw [abs_mul,abs_mul]
      calc _ ≤ ((1/20:ℝ)*‖v‖)*‖v‖ := mul_le_mul
             (mul_le_mul ((af.2 i j).trans scale) (vi i) (abs_nonneg _) (by norm_num))
             (vi j) (abs_nonneg _) (by positivity)
           _ = _ := by ring
    have flat : (∑ i : Fin 3, ∑ j : Fin 3, δ i j*v i*v j) = ‖v‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp +decide [Fin.sum_univ_three,δ,Matrix.one_apply] <;> ring
    let H := ∑ i : Fin 3, ∑ j : Fin 3, c.h x i j*v i*v j
    have dev : |H-‖v‖^2| ≤ 9/20*‖v‖^2 := calc
      _ = |∑ i : Fin 3, ∑ j : Fin 3, (c.h x i j-δ i j)*v i*v j| := by
        rw [← flat]; dsimp only [H];simp only [sub_mul,Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, (c.h x i j-δ i j)*v i*v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (1/20:ℝ)*‖v‖^2 := Finset.sum_le_sum fun i _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => comp i j)
      _ = _ := by simp [Fin.sum_univ_three]; ring
    have hlow : (1/2:ℝ)*‖v‖^2 ≤ H := by linarith only [(abs_le.mp dev).1,sq_nonneg ‖v‖]
    have prod := mul_le_mul wlow hlow (by positivity : 0 ≤ (1/2:ℝ)*‖v‖^2) (by positivity : 0 ≤ w^4)
    calc ‖v‖^2/4 ≤ w^4*H := by linarith only [prod]
         _ = _ := by dsimp only [staticPositiveMetric,w,H];simp only [Finset.mul_sum]; apply Finset.sum_congr rfl
                     intro i _
                     exact Finset.sum_congr rfl (fun j _ => by ring)
  refine ⟨R,rp',lower,?_⟩
  intro γ a b hab smooth far
  have maps : MapsTo γ (Icc a b) c.W := fun t ht => cover _ (far t ht)
  have cn := c.smoothLapse.continuousOn.comp smooth.continuous.continuousOn maps
  have ch (i j : Fin 3) := (c.smoothMetric i j).continuousOn.comp smooth.continuous.continuousOn maps
  have dcont := smooth.continuous_deriv le_rfl
  have vi (i : Fin 3) : Continuous (fun t => deriv γ t i) :=
    (PiLp.continuous_apply 2 _ i).comp dcont
  let Q := fun t : ℝ => ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric c.N c.h (γ t) i j * deriv γ t i * deriv γ t j
  have qc : ContinuousOn Q (Icc a b) := by
    apply continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact (((((continuousOn_const.add cn).div_const 2).pow 4).mul (ch i j)).mul
      (vi i).continuousOn).mul (vi j).continuousOn
  have scont : ContinuousOn (fun t => 2*Real.sqrt (Q t)) (Icc a b) :=
    continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn qc)
  have speed (t : ℝ) (ht : t ∈ Icc a b) : ‖deriv γ t‖ ≤ 2*Real.sqrt (Q t) := by
    have low : ‖deriv γ t‖^2/4 ≤ Q t := lower _ (far t ht) _
    have zero : 0 ≤ Q t := (by positivity : 0 ≤ ‖deriv γ t‖^2/4).trans low
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*Real.sqrt (Q t))).mp
    nlinarith only [low,Real.sq_sqrt zero]
  have ft := intervalIntegral.integral_deriv_eq_sub (fun t _ => smooth.differentiable one_ne_zero t)
    (dcont.intervalIntegrable a b)
  calc ‖γ b-γ a‖ = ‖∫ t in a..b, deriv γ t‖ := congrArg norm ft.symm
       _ ≤ ∫ t in a..b, ‖deriv γ t‖ := intervalIntegral.norm_integral_le_integral_norm hab
       _ ≤ ∫ t in a..b, 2*Real.sqrt (Q t) := intervalIntegral.integral_mono_on hab
         (dcont.norm.intervalIntegrable a b) (scont.intervalIntegrable_of_Icc hab) speed
       _ = _ := intervalIntegral.integral_const_mul 2 _
