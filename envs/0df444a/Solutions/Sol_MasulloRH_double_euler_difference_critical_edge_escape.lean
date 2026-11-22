-- Prove2me | solution 1 for MasulloRH.double_euler_difference_critical_edge_escape
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T10:25:33.918487+00:00
-- url     : https://prove2.me/submissions/3e91a93b-edd0-4e2e-be32-d946d9467ada

import Mathlib
open MeasureTheory Filter Topology Set
private theorem de_lip (u : ℝ → ℝ) (h : Differentiable ℝ u) {C : ℝ}
    (hb : ∀ x, |deriv u x| ≤ C) (x y : ℝ) : |u y-u x| ≤ C*|y-x| := by
  simpa only [Real.norm_eq_abs] using (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => h t) (fun t _ => by simpa only [Real.norm_eq_abs] using hb t)
    (mem_univ x) (mem_univ y)
private theorem de_diff (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hd : Differentiable ℝ (deriv u)) (C : ℝ) (hC : ∀ x, |deriv (deriv u) x| ≤ C)
    (x a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |u x-u (x-a)-u (x-b)+u (x-a-b)| ≤ C*a*b := by
  let g := fun z => u z - u (z-a)
  have h (z : ℝ) : HasDerivAt g (deriv u z - deriv u (z-a)) z := by
    simpa [g, Pi.sub_def, Function.comp_def] using ((hu z).hasDerivAt.sub (((hu (z-a)).hasDerivAt).comp z ((hasDerivAt_id z).sub_const a)))
  have hg : ∀ z, |deriv g z| ≤ C*a := by
    intro z
    rw [(h z).deriv]
    simpa [abs_of_nonneg ha] using de_lip (deriv u) hd hC (z-a) z
  have hh := de_lip g (fun z => (h z).differentiableAt) hg (x-b) x
  simpa [g,sub_sub,add_comm,add_left_comm,add_assoc,abs_of_nonneg hb,sub_eq_add_neg] using hh

theorem solution (u : ℝ → ℝ) (hu : Differentiable ℝ u) (hd : Differentiable ℝ (deriv u))
    (K : ℝ) (hK : 0 ≤ K) (hcurv : ∀ y, |deriv (deriv u) y| ≤ K)
    (hs : ∀ y ∉ Icc (-2:ℝ) (-1), u y = 0) (hm : (∫ y : ℝ, u y) = 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let h := fun T x : ℝ => Real.exp (x/2) * u (x/T) / T
    let D := fun T x : ℝ => h T x - Real.exp (a/2)*h T (x-a)
        - Real.exp (b/2)*h T (x-b) + Real.exp ((a+b)/2)*h T (x-a-b)
    (∀ T : ℝ, 0 < T → (∫ x : ℝ, Real.exp (-x/2)*h T x) = 1) ∧
    Tendsto (fun T : ℝ => ∫ x : ℝ, Real.exp |x| * (1+x^2)^2 * (D T x)^2) atTop (𝓝 0) := by
  dsimp only
  let d := fun (T x : ℝ) => u (x/T)-u ((x-a)/T)-u ((x-b)/T)+u ((x-a-b)/T)
  have he (c x : ℝ) : Real.exp (c/2) * Real.exp ((x-c)/2) = Real.exp (x/2) := by
    rw [← Real.exp_add]; congr 1; ring
  constructor
  · intro T hT
    have hpoint (x : ℝ) : Real.exp (-x/2) * (Real.exp (x/2)*u (x/T)/T) = u (x/T)/T := by
      have hz : Real.exp (-x/2) * Real.exp (x/2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
      linear_combination (u (x/T)/T)*hz
    simp_rw [hpoint, div_eq_mul_inv]
    rw [integral_mul_const]
    simp_rw [mul_comm _ T⁻¹]
    rw [Measure.integral_comp_mul_left, inv_inv, abs_of_pos hT, smul_eq_mul, hm]
    field_simp
  · let E := fun T x : ℝ => Real.exp |x| * (1+x^2)^2 * (Real.exp (x/2)*d T x/T)^2
    have heq (T x : ℝ) : Real.exp (x/2)*u (x/T)/T - Real.exp (a/2)*(Real.exp ((x-a)/2)*u ((x-a)/T)/T) -
        Real.exp (b/2)*(Real.exp ((x-b)/2)*u ((x-b)/T)/T) + Real.exp ((a+b)/2)*(Real.exp ((x-a-b)/2)*u ((x-a-b)/T)/T)
        = Real.exp (x/2)*d T x/T := by
      have hh := he (a+b) x
      rw [show x-(a+b)=x-a-b by ring] at hh
      dsimp [d]; linear_combination -(u ((x-a)/T)/T)*(he a x) -(u ((x-b)/T)/T)*(he b x) + (u ((x-a-b)/T)/T)*hh
    simp_rw [heq]
    change Tendsto (fun T : ℝ => ∫ x : ℝ, E T x) atTop (𝓝 0)
    let A := (5*(K*a*b))^2
    have hbound (T : ℝ) (hT : 1 ≤ T) (hab : a+b ≤ T) :
        (∫ x : ℝ, E T x) ≤ (2*A)/T := by
      have ht : 0 < T := by linarith
      let I := Icc (-2*T) (0:ℝ)
      let M := I.indicator (fun _ => A/T^2)
      have hi : Integrable M := (integrableOn_const (s := I) (hs := isCompact_Icc.measure_ne_top)).integrable_indicator measurableSet_Icc
      have hcomp (x : ℝ) : E T x ≤ M x := by
        by_cases hx : x ∈ I
        · have hx1 := hx.1
          have hx2 := hx.2
          have hdif : |d T x| ≤ K*a*b/T^2 := by
            have hc := de_diff u hu hd K hcurv (x/T) (a/T) (b/T) (by positivity) (by positivity)
            dsimp [d]; simp only [sub_div]
            convert hc using 1 <;> ring
          have hpoly : 1+x^2 ≤ 5*T^2 := by
            nlinarith [mul_nonneg (show 0 ≤ x+2*T by linarith) (show 0 ≤ 2*T-x by linarith),
              mul_nonneg (show 0 ≤ T-1 by linarith) (show 0 ≤ T+1 by linarith)]
          have hxexp : Real.exp |x| * Real.exp (x/2)^2 = 1 := by
            rw [abs_of_nonpos hx2, sq, ← Real.exp_add, ← Real.exp_add]; ring_nf; simp
          have hh := mul_le_mul hpoly hdif (abs_nonneg _) (by positivity)
          have hH : (1+x^2)*|d T x| ≤ 5*(K*a*b) := by
            calc
              _ ≤ 5*T^2*(K*a*b/T^2) := hh
              _ = _ := by field_simp [ne_of_gt ht] <;> ring
          have hsq := pow_le_pow_left₀ (mul_nonneg (by positivity : 0 ≤ 1+x^2) (abs_nonneg _)) hH 2
          rw [mul_pow,sq_abs] at hsq
          dsimp [E,M,A]
          rw [Set.indicator_of_mem hx,div_pow,mul_pow]
          calc
            _ = (Real.exp |x| * Real.exp (x/2)^2) * ((1+x^2)^2 * d T x^2) / T^2 := by ring
            _ ≤ _ := by rw [hxexp,one_mul]; exact div_le_div_of_nonneg_right hsq (sq_nonneg _)
        · have hzero (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ T) : u ((x-c)/T)=0 := by
            apply hs; intro hy; apply hx
            rw [Set.mem_Icc] at hy
            have hh := (le_div_iff₀ ht).mp hy.1
            have hh' := (div_le_iff₀ ht).mp hy.2
            exact ⟨by linarith,by linarith⟩
          have hz : u (x/T)=0 := by simpa using hzero 0 le_rfl ht.le
          have hz' := hzero (a+b) (by positivity) hab
          rw [show x-(a+b)=x-a-b by ring] at hz'
          simp [E,d,M,Set.indicator_of_notMem hx,hz,hz',hzero a ha (by linarith),hzero b hb (by linarith)]
      have hmajor := integral_mono_of_nonneg (Eventually.of_forall (fun x => by dsimp [E]; positivity : ∀ x, 0 ≤ E T x)) hi (Eventually.of_forall hcomp)
      apply hmajor.trans_eq
      dsimp [M]
      rw [integral_indicator measurableSet_Icc,setIntegral_const]
      simp [I,Real.volume_real_Icc,ht.le,A,smul_eq_mul]
      <;> field_simp <;> ring
    apply squeeze_zero' (Eventually.of_forall (fun T => integral_nonneg (fun x => by dsimp [E]; positivity)))
    · filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (a+b)] with T hT hab
      exact hbound T hT hab
    · exact tendsto_const_nhds.div_atTop tendsto_id
