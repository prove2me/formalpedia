-- Prove2me | solution 1 for MasulloRH.approximate_prime_certificate_bounds_missing_zero_mass
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:04:24.636278+00:00
-- url     : https://prove2.me/submissions/00828901-e9a6-4439-986f-3caa75f901f7

-- Extends the quantitative missing-zero estimate to certificates with additive slack.
-- The logarithmic tail envelope is adapted from the cutoff proof of marozols.
import Theorems.Thm_MasulloRH_prime_mass_deficit_comparable_to_omitted_zero_weight
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction
open Set Filter Topology MeasureTheory

private theorem mangoldt_tail_envelope (N : ℕ) (hN : 2 ≤ N) :
    Summable (fun n : ℕ => Real.log ↑(n+N+1) * (↑(n+N+1):ℝ)^(-(5/2):ℝ)) ∧
    ∑' n : ℕ, Real.log ↑(n+N+1) * (↑(n+N+1):ℝ)^(-(5/2):ℝ) ≤
      ((2/3)*Real.log N+4/9)*(N:ℝ)^(-(3/2):ℝ) := by
  let g (x : ℝ) := Real.log x*x^(-(5/2):ℝ)
  let P (x : ℝ) := -((2/3)*Real.log x+4/9)*x^(-(3/2):ℝ)
  have hxN : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hg (x : ℝ) (hx : 0 < x) : HasDerivAt g
      ((1-(5/2)*Real.log x)*x^(-(7/2):ℝ)) x := by
    have d := (Real.hasDerivAt_log hx.ne').mul
      (Real.hasDerivAt_rpow_const (p:=-(5/2)) (.inl hx.ne'))
    apply d.congr_deriv
    rw [show (-(5/2):ℝ)-1 = -(7/2) by norm_num,
      show x^(-(5/2):ℝ) = x^(-(7/2):ℝ)*x by
        rw [←Real.rpow_add_one hx.ne']; norm_num]
    field_simp
    ring
  have hP (x : ℝ) (hx : x ∈ Ici (N:ℝ)) : HasDerivAt P (g x) x := by
    have hx0 : 0 < x := by change (N:ℝ) ≤ x at hx; linarith
    have d := ((((Real.hasDerivAt_log hx0.ne').const_mul (2/3)).add_const (4/9)).neg).mul
      (Real.hasDerivAt_rpow_const (p:=-(3/2)) (.inl hx0.ne'))
    apply d.congr_deriv
    dsimp [g]
    rw [show (-(3/2):ℝ)-1 = -(5/2) by norm_num,
      show x^(-(3/2):ℝ) = x^(-(5/2):ℝ)*x by
        rw [←Real.rpow_add_one hx0.ne']; norm_num]
    field_simp
    ring
  have anti : AntitoneOn g (Ici (N:ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro x hx
      exact (hg x (lt_of_lt_of_le (by linarith) hx)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hg x (lt_of_lt_of_le (by linarith) (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxn : (N:ℝ) ≤ x := interior_subset hx
      have hx0 : 0 < x := by linarith
      have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) (hxN.trans hxn)
      rw [(hg x hx0).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.log_two_gt_d9])
        (Real.rpow_nonneg hx0.le _)
  have hpos (x : ℝ) (hx : x ∈ Ioi (N:ℝ)) : 0 ≤ g x := by
    change (N:ℝ) < x at hx
    exact mul_nonneg (Real.log_nonneg (by linarith)) (Real.rpow_nonneg (by linarith) _)
  have hloglim := (isLittleO_log_rpow_atTop (r:=3/2) (by norm_num)).tendsto_div_nhds_zero
  have hpow := tendsto_rpow_neg_atTop (y:=3/2) (by norm_num)
  have hlim : Tendsto P atTop (𝓝 0) := by
    have h := ((hloglim.const_mul (2/3)).add (hpow.const_mul (4/9))).neg
    simp only [mul_zero,add_zero,neg_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    dsimp [P]
    rw [Real.rpow_neg hx.le]
    ring
  have hi := integrableOn_Ioi_deriv_of_nonneg' hP hpos hlim
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hP hpos hlim
  constructor
  · have hS := AntitoneOn.summable_of_integrableOn_Ioi anti hi hpos
    simpa [g,Nat.add_assoc] using (summable_nat_add_iff (N+1)).mpr hS
  · calc _ ≤ ∫ x in Ioi (N:ℝ), g x := AntitoneOn.tsum_comp_add_le_integral N anti hi hpos
         _ = _ := by rw [he]; dsimp [P]; ring



theorem solution (N : ℕ) (hN : 2 ≤ N) (ε : ℝ)
    (F : Finset (ZetaZerosInTraceStrip (1/2))) (hF : ∀ z ∈ F, z.val.re = 1/2)
    (hc : Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑ j ∈ Finset.range (N+1), (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
        (∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))) + ε) :
    (∑' z : ZetaZerosInTraceStrip (1/2), if z ∈ F then 0 else zeroDecayWeight (1/2) z) ≤
      4*(ε + ((2/3)*Real.log N+4/9)*(N:ℝ)^(-(3/2):ℝ)) := by
  classical
  let f (j : ℕ) := vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)
  have hs : Summable f := regularized_reference_mass_prime_series.summable
  obtain ⟨henv,hbound⟩ := mangoldt_tail_envelope N hN
  let g := fun k : ℕ => Real.log ↑(k+N+1) * (↑(k+N+1):ℝ)^(-(5/2):ℝ)
  have hm (k : ℕ) : f (k+(N+1)) ≤ g k := by
    let j := k+N+1
    have hj : k+(N+1) = j := by dsimp [j]; omega
    rw [hj]
    change _ ≤ Real.log j * (j:ℝ)^(-(5/2):ℝ)
    rw [Real.rpow_neg (Nat.cast_nonneg _),←div_eq_mul_inv]
    exact (sub_le_self _ (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg j.cast_nonneg _))).trans
      (div_le_div_of_nonneg_right vonMangoldt_le_log (by positivity))
  have htail := ((summable_nat_add_iff (N+1)).mpr hs).tsum_le_tsum hm henv
  have he := hs.sum_add_tsum_nat_add (N+1)
  have hdef := (prime_mass_deficit_comparable_to_omitted_zero_weight F hF).1
  let C := Real.log 2/2 + Real.pi/4 - 37/30
  let M := ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
    ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
  change _ / 4 ≤ C + (∑' j, f j) - M at hdef
  change C + (∑ j ∈ Finset.range (N+1), f j) ≤ M + ε at hc
  change (∑' k,g k) ≤ _ at hbound
  linarith only [htail,hbound,he,hdef,hc]
