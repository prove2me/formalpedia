-- Prove2me | solution 1 for NoHair.regular_static_inverted_pole_uniform_ellipticity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:41:17.015282+00:00
-- url     : https://prove2.me/submissions/0b8cb8c0-82f9-435d-a52f-d153a49aff90

import Theorems.Thm_NoHair_regular_static_lapse_positive_monopole
import Theorems.Thm_NoHair_static_negative_sheet_pole_from_lapse_monopole

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

private abbrev X := ADMPoint
private abbrev I := Fin 3
private abbrev Mat := Matrix I I ℝ
private lemma pair_id (v w : X) : (∑ i : I, ∑ j : I,(1:Mat) i j*v i*w j)=inner ℝ v w := by
  simp [Matrix.one_apply,ite_mul,PiLp.inner_apply,Real.inner_apply,mul_comm]
private lemma flat_norm (v : X) : (∑ i : I, ∑ j : I,(1:Mat) i j*v i*v j)=‖v‖^2 :=
  (pair_id v v).trans (real_inner_self_eq_norm_sq _)

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ μ δ : ℝ, 0 < μ ∧ 0 < δ ∧ HasStaticLapseMonopole N μ ∧
      HasContinuousStaticPole N h μ ∧ ∀ y : ADMPoint, 0 < ‖y‖ → ‖y‖ < δ →
      ∀ v : ADMPoint,
        let Q := ∑ i : Fin 3, ∑ j : Fin 3, staticInvertedNegativeMetric N h y i j * v i * v j
        (μ/2)^4/2 * ‖v‖^2 ≤ Q ∧ Q ≤ 2*(μ/2)^4 * ‖v‖^2 := by
  obtain ⟨μ,hμ,hm⟩:=regular_static_lapse_positive_monopole Ω W N h c
  have hp:=static_negative_sheet_pole_from_lapse_monopole Ω W N h c μ hm
  let g:=staticInvertedNegativeMetric N h
  let k:=(μ/2)^4
  have hk : 0<k := by dsimp [k]; positivity
  have close : ∀ᶠ y : X in 𝓝[≠] (0:X),∀ i j : I, |g y i j-k*(1:Mat) i j| < k/18 := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp (hp i j) (k/18) (by positivity)
  obtain ⟨δ,hδ,hd⟩:=Metric.nhdsWithin_basis_ball.eventually_iff.mp close
  refine ⟨μ,δ,hμ,hδ,hm,hp,?_⟩
  intro y hy hyr v
  have off : y∈({0} : Set X)ᶜ := by simpa using norm_pos_iff.mp hy
  have bounds := hd (show y∈ball 0 δ ∩ ({0} : Set X)ᶜ from ⟨mem_ball_zero_iff.mpr hyr,off⟩)
  let E:=fun i j : I => (g y i j-k*(1:Mat) i j)*v i*v j
  have ev (i j : I) : |E i j| ≤ (k/18)*‖v‖^2 := by
    dsimp [E]
    rw [abs_mul,abs_mul,pow_two,← mul_assoc]
    exact mul_le_mul (mul_le_mul (bounds i j).le (PiLp.norm_apply_le v i) (abs_nonneg _) (by positivity))
      (PiLp.norm_apply_le v j) (abs_nonneg _) (by positivity)
  have eb : |∑ i : I,∑ j : I,E i j| ≤ k/2*‖v‖^2 := by
    calc
      _ ≤ ∑ i : I, |∑ j : I,E i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : I,∑ _j : I,(k/18)*‖v‖^2 := Finset.sum_le_sum (fun i _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ev i j))
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have val : (∑ i : I,∑ j : I,g y i j*v i*v j)-k*‖v‖^2=∑ i : I,∑ j : I,E i j := by
    rw [← flat_norm v]
    simp only [E,Fin.sum_univ_three]
    ring
  rw [← val,abs_le] at eb
  change k/2*‖v‖^2 ≤ (∑ i : I,∑ j : I,g y i j*v i*v j) ∧ _ ≤ 2*k*‖v‖^2
  constructor <;> linarith only [eb.1,eb.2,mul_nonneg hk.le (sq_nonneg ‖v‖)]
