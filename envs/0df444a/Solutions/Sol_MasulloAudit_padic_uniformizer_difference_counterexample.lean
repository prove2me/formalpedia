-- Prove2me | solution 1 for MasulloAudit.padic_uniformizer_difference_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:36:24.822308+00:00
-- url     : https://prove2.me/submissions/9c6137f6-288e-493c-9b97-adb1c3860e8a

import Mathlib

open Filter Set Metric Topology Bornology
open scoped Padic
noncomputable section

/-- A difference supported on the unit sphere has the same value in every unit direction. -/
private theorem radial_jump {K : Type*} [NormedField K] [ProperSpace K]
    (π : K) (hπ : π ≠ 0) (hsmall : ‖π‖ < 1) (f : K → ℂ) (hf : Continuous f)
    (hinf : Tendsto f (cocompact K) (𝓝 0))
    (hoff : ∀ x : K, ‖x‖ ≠ 1 → f x - f (π⁻¹*x) = 0)
    (u : K) (hu : ‖u‖ = 1) : f u - f (π⁻¹*u) = f 0 := by
  have hpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ
  have hinv : 1 < ‖π⁻¹‖ := by rw [norm_inv]; exact (one_lt_inv₀ hpos).mpr hsmall
  have inside (n : ℕ) : f (π^n*u) = f u := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : ‖π^(n+1)*u‖ < 1 := by
        rw [norm_mul,norm_pow,hu,mul_one]
        exact pow_lt_one₀ hpos.le hsmall (by omega)
      have he := sub_eq_zero.mp (hoff _ hn.ne)
      rw [pow_succ',mul_assoc,inv_mul_cancel_left₀ hπ] at he
      simpa only [pow_succ',mul_assoc] using he.trans ih
  have outside (n : ℕ) : f ((π⁻¹)^(n+1)*u) = f (π⁻¹*u) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : 1 < ‖(π⁻¹)^(n+1)*u‖ := by
        rw [norm_mul,norm_pow,hu,mul_one]
        exact one_lt_pow₀ hinv (by omega)
      have he := sub_eq_zero.mp (hoff _ hn.ne')
      rw [pow_succ' _ (n+1),mul_assoc]
      exact he.symm.trans ih
  have hto : Tendsto (fun n : ℕ => π^n*u) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hsmall).mul_const u
  have haway : Tendsto (fun n : ℕ => (π⁻¹)^(n+1)*u) atTop (cocompact K) := by
    rw [←cobounded_eq_cocompact, ←tendsto_norm_atTop_iff_cobounded]
    simp only [norm_mul,norm_pow,hu,mul_one]
    exact (tendsto_pow_atTop_atTop_of_one_lt hinv).comp (tendsto_add_atTop_nat 1)
  have h1 : f u = f 0 := tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds
    (hf.continuousAt.tendsto.comp hto) (Eventually.of_forall fun n => (inside n).symm)
  have h2 : f (π⁻¹*u) = 0 := tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds
    (hinf.comp haway) (Eventually.of_forall fun n => (outside n).symm)
  rw [h1,h2,sub_zero]

private abbrev K := ℚ_[3]
private def B : Set K := ball 1 1
private def test : K → ℂ := B.indicator (fun _ => 1)
private theorem test_lc : IsLocallyConstant test :=
  (LocallyConstant.charFn ℂ (IsUltrametricDist.isClopen_ball (1:K) 1)).isLocallyConstant
private theorem test_compact : HasCompactSupport test := by
  refine HasCompactSupport.intro (isCompact_closedBall (1:K) 1) ?_
  intro x hx; exact indicator_of_notMem (fun hy => hx (ball_subset_closedBall hy)) _
private theorem unit_of_mem {x : K} (hx : x∈B) : ‖x‖=1 := by
  have h : ‖x-1‖<‖(1:K)‖ := by simpa only [B,norm_one,mem_ball,dist_eq_norm] using hx
  simpa only [norm_one] using Padic.norm_eq_of_norm_sub_lt_right h
private theorem test_off (x : K) (hx : ‖x‖≠1) : test x=0 :=
  indicator_of_notMem (fun hy => hx (unit_of_mem hy)) _
private theorem test_one : test 1=1 :=
  indicator_of_mem (mem_ball_self (by norm_num : (0:ℝ)<1)) _
private theorem test_neg_one : test (-1)=0 := by
  apply indicator_of_notMem
  intro h
  have hh : ‖(-1:K)-1‖<1 := by simpa only [B,mem_ball,dist_eq_norm] using h
  rw [show (-1:K)-1 = -(2:ℕ) by norm_num, norm_neg] at hh
  exact (by decide : ¬3∣2) ((Padic.norm_natCast_lt_one_iff).mp hh)

theorem solution :
    (∀ (p : ℕ) [Fact p.Prime] (f : ℚ_[p] → ℂ), Continuous f →
      Tendsto f (cocompact ℚ_[p]) (𝓝 0) →
      (∀ x : ℚ_[p], ‖x‖≠1 → f x-f ((p:ℚ_[p])⁻¹*x)=0) →
      ∀ u : ℚ_[p], ‖u‖=1 → f u-f ((p:ℚ_[p])⁻¹*u)=f 0) ∧
    ∃ g : ℚ_[3] → ℂ, IsLocallyConstant g ∧ HasCompactSupport g ∧ g 0=0 ∧
      g 1=1 ∧ g (-1)=0 ∧
      (∀ (f : ℚ_[3] → ℂ), Continuous f → Tendsto f (cocompact ℚ_[3]) (𝓝 0) →
        ¬∀ x : ℚ_[3], f x-f ((3:ℚ_[3])⁻¹*x)=g x) ∧
      (fun x : ℚ_[3] => g x-g ((3:ℚ_[3])⁻¹*x)) ≠
        (fun x : ℚ_[3] => g x-g ((-3:ℚ_[3])⁻¹*x)) := by
  constructor
  · intro p hp f hf hinf hoff u hu
    exact radial_jump _ (by exact_mod_cast hp.out.ne_zero) Padic.norm_p_lt_one f hf hinf hoff u hu
  refine ⟨test,test_lc,test_compact,test_off 0 (by norm_num),test_one,test_neg_one,?_,?_⟩
  · intro f hf hinf he
    have hπ : (3:K)≠0 := by norm_num
    have hs : ‖(3:K)‖<1 := Padic.norm_p_lt_one
    have hu (u : K) (hu : ‖u‖=1) : test u=f 0 := by
      rw [←he]; exact radial_jump _ hπ hs f hf hinf (fun x hx => (he x).trans (test_off x hx)) u hu
    have h := (hu 1 (by simp)).trans (hu (-1) (by simp)).symm
    simpa [test_one,test_neg_one] using h
  · intro eq
    have h := congrFun eq (3:K)
    have hπ : (3:K)≠0 := by norm_num
    have hneg : (-3:K)⁻¹*(3:K) = -1 := by field_simp <;> norm_num
    simp only [inv_mul_cancel₀ hπ,hneg,test_one,test_neg_one] at h
    exact one_ne_zero (sub_right_inj.mp h)
