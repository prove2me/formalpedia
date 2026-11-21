-- Prove2me | solution 1 for MasulloRH.critical_line_mass_has_explicit_verification_height
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:52:48.238468+00:00
-- url     : https://prove2.me/submissions/02bdcd00-bd8f-4001-a129-1bc499218bd8

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Theorems.Thm_MasulloRH_zero_decay_tail_at_real_lattice
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Mathlib

open Set Filter Topology MeasureTheory ArithmeticFunction Finset
open MasulloRH

private theorem ordinate_bound (ρ : ZetaZerosInTraceStrip (1/2)) : 6 < |ρ.val.im| :=
  lt_of_not_ge fun h => ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six
    ρ.prop.2.1 ρ.prop.2.2.1 h ρ.prop.1

private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin

private theorem resolvent_norm_bound (ρ : ZetaZerosInTraceStrip (1/2)) :
    ‖zeroResolventTerm (1/2) 3 ρ‖ ≤ zeroDecayWeight (1/2) ρ := by
  let z := ρ.val
  have hy : 6 < |z.im| := ordinate_bound ρ
  have ha : |z.im| ≤ ‖3-z‖ := by simpa using Complex.abs_im_le_norm (3-z)
  have hb : |z.im| ≤ ‖5/2-z‖ := by simpa using Complex.abs_im_le_norm (5/2-z)
  have ha0 : 0 < ‖3-z‖ := by linarith
  have hb0 : 0 < ‖5/2-z‖ := by linarith
  have hid : 1/(3-z) - 1/(5/2-z) = (-1/2)/((3-z)*(5/2-z)) := by
    rw [div_sub_div _ _ (norm_pos_iff.mp ha0) (norm_pos_iff.mp hb0)]
    congr 1
    ring
  change ‖(analyticOrderNatAt riemannZeta z : ℂ) * _‖ ≤ _
  rw [hid, norm_mul, Complex.norm_natCast, norm_div, norm_mul]
  change _ ≤ (analyticOrderNatAt riemannZeta z : ℝ)/(1+z.im^2)
  rw [div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [show ‖(-1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num [norm_div]]
  rw [← div_eq_mul_one_div, ← one_div (1 + z.im^2)]
  apply (div_le_div_iff₀ (mul_pos ha0 hb0) (by positivity)).mpr
  have hmul := mul_le_mul ha hb (abs_nonneg _) ha0.le
  have hy' : 1 ≤ z.im^2 := by nlinarith [sq_abs z.im, sq_nonneg (|z.im|-1)]
  nlinarith [sq_abs z.im]

private theorem line_kernel (z : ZetaZerosInTraceStrip (1/2)) (hz : z.val.re = 1/2) :
    (zeroResolventTerm (1/2) 3 z).re = (analyticOrderNatAt riemannZeta z.val:ℝ) *
      ((z.val.im^2 - 5) / (2 * (z.val.im^2 + 25/4) * (z.val.im^2+4))) := by
  unfold zeroResolventTerm
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  congr 1
  simp only [one_div,Complex.sub_re,Complex.inv_re,Complex.normSq_apply,Complex.sub_im]
  norm_num [hz,pow_two,Complex.div_ofNat_re,Complex.div_ofNat_im]
  field_simp
  ring


private theorem finite_zeros_to_height (H : ℝ) (hH : 0 ≤ H) :
    {z : ZetaZerosInTraceStrip (1/2) | |z.val.im| ≤ H}.Finite := by
  let w := zeroDecayWeight (1/2)
  have hlim : Tendsto w cofinite (𝓝 0) := (weighted_zero_summability (1/2) (by norm_num)).tendsto_cofinite_zero
  have he := hlim.eventually (gt_mem_nhds (show (0:ℝ) < 1/(1+H^2) by positivity))
  have hbad : {z | ¬ w z < 1/(1+H^2)}.Finite := by
    simpa only [eventually_cofinite] using he
  apply hbad.subset
  intro z hz
  change |z.val.im| ≤ H at hz
  change ¬w z < 1/(1+H^2)
  apply not_lt.mpr
  have hysq : z.val.im^2 ≤ H^2 := by nlinarith [sq_abs z.val.im,mul_self_le_mul_self (abs_nonneg _) hz]
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta z.val := by exact_mod_cast multiplicity_pos z
  exact (one_div_le_one_div_of_le (by positivity) (by linarith only [hysq])).trans
    (div_le_div_of_nonneg_right hm (by positivity))

private theorem bounded_witness (n N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, N ≤ p)
    (hcover : ∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ 5/2+2*(n:ℝ) → z.val.re = 1/2)
    (hbudget : 2/((5/2+2*(n:ℝ))-1) * (8*((zetaLogDeriv 3).re -
      (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
      (zetaLogDeriv (5/2)).re + (1+Real.log n)/2) ≤
      ∑ p ∈ P, (ArithmeticFunction.vonMangoldt p / (p:ℝ)^(5/2:ℝ) -
        ArithmeticFunction.vonMangoldt p / (p:ℝ)^(3:ℝ))) :
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z, z ∈ F ↔ |z.val.im| ≤ 5/2+2*(n:ℝ)) ∧
      (∀ z ∈ F, z.val.re = 1/2) ∧
      Real.log 2 / 2 + Real.pi / 4 - 37 / 30 +
        (∑ j ∈ Finset.range N, (ArithmeticFunction.vonMangoldt j / (j:ℝ)^(5/2:ℝ) -
          ArithmeticFunction.vonMangoldt j / (j:ℝ)^(3:ℝ))) ≤
        ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2 - 5) / (2 * (z.val.im^2 + 25/4) * (z.val.im^2+4))) := by
  classical
  let H : ℝ := 5/2+2*n
  let C := Real.log 2/2 + Real.pi/4-37/30
  let A := (zetaLogDeriv 3).re - (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re
  let f (j : ℕ) := ArithmeticFunction.vonMangoldt j / (j:ℝ)^(5/2:ℝ) -
    ArithmeticFunction.vonMangoldt j / (j:ℝ)^(3:ℝ)
  have hpos (j : ℕ) : 0 ≤ f j := by
    rcases eq_or_ne j 0 with rfl | hj
    · simp [f]
    have h1 : 1 ≤ (j:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
  let F := (finite_zeros_to_height H (by dsimp [H]; positivity)).toFinset
  have hF (z) : z ∈ F ↔ |z.val.im| ≤ H := Set.Finite.mem_toFinset _
  have hon (z) (hz : z ∈ F) := hcover z ((hF z).mp hz)
  refine ⟨F,hF,hon,?_⟩
  let r := zeroResolventTerm (1/2) 3
  let k (z : ZetaZerosInTraceStrip (1/2)) := (r z).re
  let w := zeroDecayWeight (1/2)
  have hw := weighted_zero_summability (1/2) (by norm_num)
  have hs : Summable r := hw.of_norm_bounded resolvent_norm_bound
  have hk : Summable k := (Complex.hasSum_re hs.hasSum).summable
  have hsum : (∑' z,k z) = A := by
    dsimp only [A]
    rw [←regularized_initial_identity_full_strip (3:ℂ) (by norm_num)]
    change _ = ((_ + ∑' z,r z).re-_)
    rw [Complex.add_re,add_sub_cancel_left,Complex.re_tsum hs]
  let E : Set (ZetaZerosInTraceStrip (1/2)) := (F : Set _)ᶜ
  have hsplit : (∑ z ∈ F,k z)+(∑' z,E.indicator k z) = A := by
    rw [←_root_.tsum_subtype]
    exact (hk.sum_add_tsum_compl (s:=F)).trans hsum
  have htail : (∑' z,E.indicator k z) ≤ ∑' z,E.indicator w z := by
    apply (hk.indicator E).tsum_le_tsum _ (hw.indicator E)
    intro z
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz]
      exact (Complex.re_le_norm _).trans (resolvent_norm_bound z)
    · simp only [Set.indicator_of_notMem hz,le_refl]
  have hweight : (∑' z,E.indicator w z) ≤ ∑ p ∈ P,f p := by
    have hrewrite (z : ZetaZerosInTraceStrip (1/2)) : E.indicator w z =
        if H < |z.val.im| then zeroDecayWeight (1/2) z else 0 := by
      have hz : z ∈ E ↔ H < |z.val.im| := by change (¬z∈F) ↔ _; rw [hF,not_le]
      simp only [Set.indicator_apply,hz,w]
    simp_rw [hrewrite]
    exact (zero_decay_tail_at_real_lattice n).trans hbudget
  have hdis : Disjoint (Finset.range N) P := Finset.disjoint_left.mpr
    (fun j hj hp => (Nat.not_lt_of_ge (hP j hp)) (Finset.mem_range.mp hj))
  have hpri := regularized_reference_mass_prime_series
  have hfp : (∑ j ∈ Finset.range N,f j)+(∑ j ∈ P,f j) ≤ A-C := by
    rw [←Finset.sum_union hdis]
    calc _ ≤ ∑' j,f j := hpri.summable.sum_le_tsum _ (fun j _ => hpos j)
         _ = A-C := by
           rw [show (∑' j,f j) = _ from hpri.tsum_eq]
           dsimp only [A,C]
           ring
  have he := htail.trans hweight
  change C+(∑ j ∈ Finset.range N,f j) ≤ _
  calc _ ≤ ∑ z ∈ F,k z := by linarith only [hsplit,he,hfp]
       _ = _ := Finset.sum_congr rfl fun z hz => line_kernel z (hon z hz)

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


private theorem interval_mangoldt_mass (X : ℕ) (hX : 4 ≤ X) :
    (X:ℝ) ≤ ∑ j ∈ Ioc X (16*X), vonMangoldt j := by
  have hXR : (4:ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : (0:ℝ) < X := by linarith
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have h17 : Real.log 17 ≤ 5*Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<17) (show (17:ℝ)≤2^5 by norm_num)
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have hl : Real.log (16*(X:ℝ)+1) ≤ 2*X := by
    have h := Real.log_le_log (by positivity : 0<16*(X:ℝ)+1)
      (show 16*(X:ℝ)+1 ≤ 17*X by linarith)
    rw [Real.log_mul (by norm_num) hx0.ne'] at h
    linarith [Real.log_le_sub_one_of_pos hx0]
  have hu := Chebyshev.psi_le_const_mul_self hx0.le
  rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hu
  have hd := Chebyshev.psi_ge (16*X)
  push_cast at hd
  have he : Chebyshev.psi X + ∑ j ∈ Ioc X (16*X), vonMangoldt j = Chebyshev.psi (16*X:ℕ) := by
    simp only [Chebyshev.psi,Nat.floor_natCast]
    rw [←sum_union (Ioc_disjoint_Ioc_of_le (le_refl X)), Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le X) (by omega)]
  have hupper : Chebyshev.psi X ≤ 6*X := hu.trans <| mul_le_mul_of_nonneg_right (by norm_num;linarith) hx0.le
  have hl2 : (2/3:ℝ)*X ≤ Real.log 2*X := mul_le_mul_of_nonneg_right (by linarith) hx0.le
  push_cast at he
  linarith

private theorem reserve (X : ℕ) (hX : 4 ≤ X) :
    1/(2048*(X:ℝ)^(3/2:ℝ)) ≤ ∑ j ∈ Ioc X (16*X),
      (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)) := by
  have hXR : (4:ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : 0 < (X:ℝ) := by linarith
  have h16 : (16:ℝ)^(5/2:ℝ) = 1024 := by
    rw [show (5/2:ℝ)=2+1/2 by norm_num,Real.rpow_add (by norm_num),
      ←Real.sqrt_eq_rpow, Real.rpow_ofNat]
    norm_num
  have ha : (16*(X:ℝ))^(5/2:ℝ) = 1024*((X:ℝ)^(3/2:ℝ))*(X:ℝ) := by
    rw [Real.mul_rpow (by norm_num) hx0.le,h16,
      show (5/2:ℝ)=3/2+1 by norm_num,Real.rpow_add_one hx0.ne']; ring
  have he : 1/(2048*(X:ℝ)^(3/2:ℝ)) = (X:ℝ)/(2*(16*(X:ℝ))^(5/2:ℝ)) := by
    rw [ha]; field_simp [hx0.ne',(Real.rpow_pos_of_pos hx0 (3/2:ℝ)).ne']; ring
  rw [he]
  apply (div_le_div_of_nonneg_right (interval_mangoldt_mass X hX) (by positivity)).trans
  rw [sum_div]
  apply sum_le_sum
  intro j hj
  obtain ⟨hjlo,hjhi⟩ := mem_Ioc.mp hj
  have hj0 : 0 < (j:ℝ) := by exact_mod_cast (show 0<j by omega)
  have hjr : (j:ℝ) ≤ 16*(X:ℝ) := by exact_mod_cast hjhi
  have hs : (2:ℝ) ≤ Real.sqrt j := (Real.le_sqrt (by norm_num) hj0.le).mpr
    (by exact_mod_cast (show 2^2≤j by omega))
  have hp := Real.rpow_le_rpow hj0.le hjr (by norm_num : 0 ≤ (5/2:ℝ))
  have hm : (j:ℝ)^(5/2:ℝ) * Real.sqrt j = (j:ℝ)^3 := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hj0,show (5/2:ℝ)+1/2=3 by norm_num,Real.rpow_ofNat]
  apply (div_le_div_of_nonneg_left (vonMangoldt_nonneg (n:=j)) (by positivity) (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2))).trans
  rw [Real.rpow_ofNat,←hm]
  field_simp [(Real.rpow_pos_of_pos hj0 (5/2:ℝ)).ne',(Real.sqrt_pos.mpr hj0).ne']
  nlinarith [mul_nonneg (vonMangoldt_nonneg (n:=j)) (sub_nonneg.mpr hs)]


private theorem budget_for_height (X : ℝ) (hX : 4 ≤ X) :
    let n := ⌈16384*X^(3/2:ℝ)*(1+Real.log X)⌉₊
    2/((5/2+2*(n:ℝ))-1)*(9/2+(1+Real.log n)/2) ≤ 1/(2048*X^(3/2:ℝ)) := by
  let n := ⌈16384*X^(3/2:ℝ)*(1+Real.log X)⌉₊
  change 2/((5/2+2*(n:ℝ))-1)*(9/2+(1+Real.log n)/2) ≤ _
  have hx : 0 < X := by linarith
  have hlog := Real.log_nonneg (by linarith : 1 ≤ X)
  have hp := Real.rpow_pos_of_pos hx (3/2:ℝ)
  have hnl : 16384*X^(3/2:ℝ)*(1+Real.log X) ≤ (n:ℝ) := Nat.le_ceil _
  have hn : 0 < (n:ℝ) := lt_of_lt_of_le (by positivity) hnl
  have hnu := Nat.ceil_lt_add_one (show 0 ≤ 16384*X^(3/2:ℝ)*(1+Real.log X) by positivity)
  change (n:ℝ) < _ at hnu
  have hexp : X^(3/2:ℝ) ≤ X^2 := by
    rw [←Real.rpow_natCast X 2]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlf : 1+Real.log X ≤ X := by linarith [Real.log_le_sub_one_of_pos hx]
  have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ) ≤ 16384)) hlf
      (by linarith : 0 ≤ 1+Real.log X) (by positivity : 0 ≤ 16384*X^2)
  have hX3 : 1 ≤ X^3 := one_le_pow₀ (by linarith : 1 ≤ X)
  have hX8 : 16385 ≤ X^8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hX 8
    norm_num at h
    linarith
  have hb : (n:ℝ) ≤ X^11 := by
    rw [show (11:ℕ)=8+3 by decide,pow_add]
    have h := mul_le_mul_of_nonneg_right hX8 (by positivity : 0 ≤ X^3)
    nlinarith only [h,hmul,hnu,hX3]
  have hlogn := Real.log_le_log hn hb
  rw [Real.log_pow] at hlogn
  have hnum : (9/2+(1+Real.log n)/2) ≤ 6*(1+Real.log X) := by norm_num at hlogn; linarith
  have hden : 0 < (5/2+2*(n:ℝ))-1 := by linarith
  have hfrac : 2/((5/2+2*(n:ℝ))-1) ≤ 1/(n:ℝ) := by
    apply (div_le_div_iff₀ hden hn).mpr; linarith
  have hln := Real.log_nonneg (show 1 ≤ (n:ℝ) by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hn.ne'))
  apply (mul_le_mul hfrac hnum (by linarith) (by positivity)).trans
  rw [one_div_mul_eq_div]
  apply (div_le_div_iff₀ hn (by positivity)).mpr
  nlinarith only [hnl, mul_nonneg hp.le (by linarith : 0 ≤ 1+Real.log X)]


theorem solution (N : ℕ) :
    let X := (N:ℝ)+4
    let n := ⌈16384*X^(3/2:ℝ)*(1+Real.log X)⌉₊
    let H := (5/2:ℝ)+2*(n:ℝ)
    (∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ H → z.val.re = 1/2) →
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z, z ∈ F ↔ |z.val.im| ≤ H) ∧ (∀ z ∈ F, z.val.re = 1/2) ∧
      Real.log 2/2 + Real.pi/4 - 37/30 +
        (∑ j ∈ Finset.range N, (vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
        ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4))) := by
  let X : ℕ := N+4
  have hX : 4 ≤ X := by dsimp [X]; omega
  have hcast : (X:ℝ) = (N:ℝ)+4 := by simp [X]
  let n := ⌈16384*(X:ℝ)^(3/2:ℝ)*(1+Real.log X)⌉₊
  change (∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ _ → z.val.re = 1/2) → _
  simp only [←hcast]
  intro cover
  apply bounded_witness n N (Finset.Ioc X (16*X))
  · intro p hp; have := (Finset.mem_Ioc.mp hp).1; dsimp [X] at this; omega
  · exact cover
  · have hb := budget_for_height (X:ℝ) (by exact_mod_cast hX)
    change 2/((5/2+2*(n:ℝ))-1)*(9/2+(1+Real.log n)/2) ≤ _ at hb
    apply le_trans _ (hb.trans (reserve X hX))
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
    linarith only [reference_bound]

