-- Prove2me | solution 1 for MasulloRH.critical_line_mass_dominates_finite_prime_sums
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T01:55:54.552119+00:00
-- url     : https://prove2.me/submissions/f0b2bfab-d211-4245-bfce-7428b0a5a24d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Theorems.Thm_MasulloRH_critical_line_mass_of_verified_height_and_prime_tail
import Theorems.Thm_MasulloRH_prime_height_critical_zero_count_certificates
import Mathlib

open Set Filter Topology MeasureTheory ArithmeticFunction MasulloRH

private theorem mangoldt_series_hasSum {x : ℝ} (hx : 1 < x) :
    HasSum (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n:ℝ)^x)
      (-(zetaLogDeriv (x:ℂ)).re) := by
  have hs : 1 < (x:ℂ).re := hx
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum
  have hv := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change LSeries _ (x:ℂ) = _ at hv
  change HasSum _ (LSeries _ (x:ℂ)) at h
  rw [hv,neg_div] at h
  have hR := Complex.hasSum_re h
  convert hR using 1
  · ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · change _ = (LSeries.term (fun k : ℕ => (ArithmeticFunction.vonMangoldt k:ℂ)) (x:ℂ) n).re
      rw [LSeries.term_of_ne_zero hn]
      simp only [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow n.cast_nonneg,
        ← Complex.ofReal_div, Complex.ofReal_re]
  · simp [zetaLogDeriv]

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


private theorem reference_bound :
    8*((zetaLogDeriv 3).re-(zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
      (zetaLogDeriv (5/2)).re ≤ 9/2 := by
  let l (j : ℕ) := vonMangoldt j/(j:ℝ)^(5/2:ℝ)
  have hal := mangoldt_series_hasSum (x:=5/2) (by norm_num)
  push_cast at hal
  have hL : -(zetaLogDeriv (5/2)).re ≤ 1/2 := by
    obtain ⟨hs,ht⟩ := mangoldt_tail_envelope 2 (by decide)
    have hp (k : ℕ) : l (k+3) ≤ Real.log ↑(k+2+1) * (↑(k+2+1):ℝ)^(-(5/2):ℝ) := by
      change vonMangoldt (k+3)/(↑(k+3):ℝ)^(5/2:ℝ) ≤ _
      rw [show k+2+1 = k+3 by omega,Real.rpow_neg (Nat.cast_nonneg _),←div_eq_mul_inv]
      exact div_le_div_of_nonneg_right vonMangoldt_le_log (by positivity)
    have hsum : Summable l := hal.summable
    have htail := ((summable_nat_add_iff 3).mpr hsum).tsum_le_tsum hp hs
    have hsplit := hsum.sum_add_tsum_nat_add 3
    rw [show (∑' j,l j) = _ from hal.tsum_eq] at hsplit
    have hp2 : (∑ j ∈ Finset.range 3,l j) = Real.log 2/(2:ℝ)^(5/2:ℝ) := by
      norm_num [Finset.sum_range_succ,l,vonMangoldt_apply_prime (by decide : Nat.Prime 2)]
    rw [hp2] at hsplit
    have hroot : (7/5:ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have h2 : (2:ℝ)^(5/2:ℝ) = 4*Real.sqrt 2 := by
      rw [show (5/2:ℝ) = 2+1/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_two,←Real.sqrt_eq_rpow]
      ring
    have h3 : (2:ℝ)^(-(3/2):ℝ) = 1/(2*Real.sqrt 2) := by
      rw [Real.rpow_neg (by norm_num),show (3/2:ℝ) = 1+1/2 by norm_num,
        Real.rpow_add (by norm_num),Real.rpow_one,←Real.sqrt_eq_rpow,one_div]
    rw [h2] at hsplit
    norm_num only [Nat.cast_ofNat] at ht
    rw [h3] at ht
    have b2 : Real.log 2/(4*Real.sqrt 2) ≤ (7/10)/(4*(7/5):ℝ) :=
      div_le_div₀ (by norm_num) (by linarith [Real.log_two_lt_d9]) (by norm_num) (by linarith)
    have b3 : (2/3*Real.log 2+4/9)*(1/(2*Real.sqrt 2)) ≤
        (2/3*(7/10)+4/9)/(2*(7/5):ℝ) := by
      rw [←div_eq_mul_one_div]
      exact div_le_div₀ (by norm_num) (by linarith [Real.log_two_lt_d9]) (by norm_num) (by linarith)
    linarith only [b2,b3,hsplit,htail,ht]
  have hC : Real.log 2/2 + Real.pi/4 -37/30 ≤ 0 := by linarith [Real.log_two_lt_d9,Real.pi_lt_d4]
  have hprime := regularized_reference_mass_prime_series
  have hmono := hprime.summable.tsum_le_tsum (fun j => sub_le_self (l j)
    (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg j.cast_nonneg (3:ℝ)))) hal.summable
  rw [hprime.tsum_eq,hal.tsum_eq] at hmono
  linarith only [hC,hL,hmono]

private theorem prime_lower (p : ℕ) (hp : p.Prime) (hp100 : 100 ≤ p) :
    4*((p.sqrt:ℝ)-1)/(p:ℝ)^3 ≤ vonMangoldt p/(p:ℝ)^(5/2:ℝ)-vonMangoldt p/(p:ℝ)^(3:ℝ) := by
  have hp100' : (100:ℝ) ≤ p := by exact_mod_cast hp100
  have hp0 : 0 < (p:ℝ) := by linarith
  have hp9 : (10:ℝ) ≤ Real.sqrt p := (Real.le_sqrt (by norm_num) hp0.le).mpr (by nlinarith)
  have hlog : (4:ℝ) ≤ Real.log p := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<3^4) (show (3:ℝ)^4 ≤ p by norm_num; linarith)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_three_gt_d9]
  have hsq : (p.sqrt:ℝ) ≤ Real.sqrt (p:ℝ) :=
    (Real.le_sqrt (by positivity) hp0.le).mpr (by exact_mod_cast Nat.sqrt_le' p)
  have he : (p:ℝ)^(5/2:ℝ) * Real.sqrt p = (p:ℝ)^3 := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hp0,show (5/2:ℝ)+1/2=3 by norm_num,Real.rpow_ofNat]
  have hkey : vonMangoldt p/(p:ℝ)^(5/2:ℝ)-vonMangoldt p/(p:ℝ)^(3:ℝ) =
      Real.log p*(Real.sqrt p-1)/(p:ℝ)^3 := by
    rw [vonMangoldt_apply_prime hp,Real.rpow_ofNat,←he]
    field_simp [hp0.ne',(Real.rpow_pos_of_pos hp0 (5/2:ℝ)).ne',(Real.sqrt_pos.mpr hp0).ne']
  rw [hkey]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc _ ≤ 4*(Real.sqrt p-1) := by linarith only [hsq]
       _ ≤ _ := mul_le_mul_of_nonneg_right hlog (by linarith)


private theorem explicit_prime_budget (p : ℕ) (hp : p.Prime) (hp100 : 100 ≤ p) :
    2 / ((5/2 + 2*((p^6 : ℕ):ℝ))-1) *
      (8*((zetaLogDeriv 3).re -
        (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
        (zetaLogDeriv (5/2)).re + (1+Real.log ((p^6 : ℕ):ℝ))/2) ≤
      vonMangoldt p / (p:ℝ)^(5/2:ℝ) - vonMangoldt p / (p:ℝ)^(3:ℝ) := by
  have hp100' : (100:ℝ) ≤ p := by exact_mod_cast hp100
  have hp0 : (0:ℝ) < p := by linarith
  have hp6 : (0:ℝ) < (p:ℝ)^6 := pow_pos hp0 _
  have hden : 0 < (5/2 + 2*(p:ℝ)^6)-1 := by linarith
  have hden_bound : 2 / ((5/2 + 2*(p:ℝ)^6)-1) ≤ 1/(p:ℝ)^6 := by
    apply (div_le_div_iff₀ hden hp6).mpr
    linarith
  have hnum : 8*((zetaLogDeriv 3).re -
        (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
        (zetaLogDeriv (5/2)).re + (1+Real.log ((p:ℝ)^6))/2 ≤ 5+3*(p:ℝ) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [reference_bound, Real.log_le_sub_one_of_pos hp0]
  have hcubic : 5+3*(p:ℝ) ≤ (p:ℝ)^3 := by
    have h := mul_nonneg
      (mul_nonneg (by linarith : (0:ℝ) ≤ (p:ℝ)-2) hp0.le)
      (by linarith : (0:ℝ) ≤ (p:ℝ)+2)
    nlinarith
  have hsqrt : (10:ℝ) ≤ p.sqrt := by
    exact_mod_cast (Nat.le_sqrt.mpr (by omega : 10*10 ≤ p))
  simp only [Nat.cast_pow]
  calc
    _ ≤ 2 / ((5/2 + 2*(p:ℝ)^6)-1) * (5+3*(p:ℝ)) :=
      mul_le_mul_of_nonneg_left hnum (div_nonneg (by norm_num) hden.le)
    _ ≤ (1/(p:ℝ)^6) * (5+3*(p:ℝ)) :=
      mul_le_mul_of_nonneg_right hden_bound (by positivity)
    _ = (5+3*(p:ℝ))/(p:ℝ)^6 := by ring
    _ ≤ 1/(p:ℝ)^3 := by
      apply (div_le_div_iff₀ hp6 (pow_pos hp0 3)).mpr
      calc
        (5+3*(p:ℝ)) * (p:ℝ)^3 ≤ (p:ℝ)^3 * (p:ℝ)^3 :=
          mul_le_mul_of_nonneg_right hcubic (by positivity)
        _ = 1*(p:ℝ)^6 := by ring
    _ ≤ 4*((p.sqrt:ℝ)-1)/(p:ℝ)^3 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ _ := prime_lower p hp hp100



theorem solution (N : ℕ) :
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z ∈ F, z.val.re = 1/2) ∧
      Real.log 2 / 2 + Real.pi / 4 - 37 / 30 +
        (∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
          ArithmeticFunction.vonMangoldt n / (n:ℝ)^(3:ℝ))) ≤
        ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2 - 5) / (2 * (z.val.im^2 + 25/4) * (z.val.im^2+4)))  := by
  classical
  obtain ⟨p, hpbig, hp⟩ := Nat.exists_infinite_primes (max N 100)
  have hpN : N ≤ p := (le_max_left _ _).trans hpbig
  have hp100 : 100 ≤ p := (le_max_right _ _).trans hpbig
  obtain ⟨F, hF, hcard⟩ := prime_height_critical_zero_count_certificates p hp hp100
  let Z : Set (ZetaZerosInTraceStrip (1/2)) :=
    {z | |z.val.im| ≤ 5/2 + 2*((p^6 : ℕ):ℝ)}
  have hsub : (F : Set (ZetaZerosInTraceStrip (1/2))) ⊆ Z := by
    intro z hz
    exact (hF z hz).2
  have heq : (F : Set (ZetaZerosInTraceStrip (1/2))) = Z :=
    F.finite_toSet.eq_of_subset_of_encard_le hsub (by simpa only [Set.encard_coe_eq_coe_finsetCard] using hcard)
  apply critical_line_mass_of_verified_height_and_prime_tail (p^6) N {p}
  · intro q hq
    have hqp : q = p := Finset.mem_singleton.mp hq
    simpa [hqp] using hpN
  · intro z hz
    have hzF : z ∈ F := by
      change z ∈ (F : Set (ZetaZerosInTraceStrip (1/2)))
      rw [heq]
      exact hz
    exact (hF z hzF).1
  · simpa only [Finset.sum_singleton] using explicit_prime_budget p hp hp100


