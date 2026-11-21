-- Prove2me | solution 1 for MasulloRH.critical_line_mass_has_reduced_verification_height
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:22:42.85417+00:00
-- url     : https://prove2.me/submissions/592f2ab1-6e64-489a-9ffa-a32d204df317

-- Finite-zero witness construction from marozols, Prove2Me submission
-- 02bdcd00-bd8f-4001-a129-1bc499218bd8. Height improvement and budget are new.
import Theorems.Thm_MasulloRH_prime_tail_reserve_to_four_mul
import Theorems.Thm_MasulloRH_certified_height_99998_reference_budget
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

private theorem reference_bound :
    8*((zetaLogDeriv 3).re-(zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
      (zetaLogDeriv (5/2)).re ≤ 7/2 := by
  have h := certified_height_99998_reference_budget.2
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<2^15) (show (2:ℝ)^15 ≤ 49998 by norm_num)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl h
  linarith only [h,hl,Real.log_two_gt_d9]

private theorem log_bound {x : ℝ} (hx : 196 ≤ x) : Real.log x ≤ (2/5)*Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hy : 14 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).mpr (by linarith)
  have h := Real.log_le_sub_one_of_pos (div_pos (Real.sqrt_pos.mpr hx0) (by norm_num : (0:ℝ)<16))
  rw [Real.log_div (Real.sqrt_pos.mpr hx0).ne' (by norm_num), Real.log_sqrt hx0.le,
    show (16:ℝ)=2^4 by norm_num,Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [Real.log_two_lt_d9]

private theorem budget_for_height (X : ℝ) (hX : 196 ≤ X) :
    let n := ⌈256*X^(3/2:ℝ)*(1+Real.log X)⌉₊
    2/((5/2+2*(n:ℝ))-1)*(7/2+(1+Real.log n)/2) ≤ 1/(128*X^(3/2:ℝ)) := by
  let n := ⌈256*X^(3/2:ℝ)*(1+Real.log X)⌉₊
  change 2/((5/2+2*(n:ℝ))-1)*(7/2+(1+Real.log n)/2) ≤ _
  have hx : 0 < X := by linarith
  have hlog := Real.log_nonneg (by linarith : 1 ≤ X)
  have hp := Real.rpow_pos_of_pos hx (3/2:ℝ)
  have hnl : 256*X^(3/2:ℝ)*(1+Real.log X) ≤ (n:ℝ) := Nat.le_ceil _
  have hn : 0 < (n:ℝ) := lt_of_lt_of_le (by positivity) hnl
  have hnu := Nat.ceil_lt_add_one (show 0 ≤ 256*X^(3/2:ℝ)*(1+Real.log X) by positivity)
  change (n:ℝ) < _ at hnu
  have hy : 14 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hx.le).mpr (by linarith)
  have hlf : 1+Real.log X ≤ Real.sqrt X/2 := by linarith [log_bound hX]
  have he : X^(3/2:ℝ) = X * Real.sqrt X := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num, Real.rpow_add hx,Real.rpow_one,←Real.sqrt_eq_rpow]
  have hpre : 256*X^(3/2:ℝ)*(1+Real.log X) ≤ 128*X^2 := calc
    _ ≤ 256*X^(3/2:ℝ)*(Real.sqrt X/2) := mul_le_mul_of_nonneg_left hlf (by positivity)
    _ = 128*X*(Real.sqrt X)^2 := by rw [he]; ring
    _ = _ := by rw [Real.sq_sqrt hx.le]; ring
  have hb : (n:ℝ) ≤ X^3 := by
    nlinarith [mul_nonneg (sq_nonneg X) (show 0 ≤ X-129 by linarith),
      one_le_pow₀ (show 1 ≤ X by linarith) (n:=2)]
  have hlogX := Real.log_le_log (by norm_num : (0:ℝ)<2^7) (show (2:ℝ)^7 ≤ X by norm_num; linarith)
  rw [Real.log_pow] at hlogX
  norm_num only [Nat.cast_ofNat] at hlogX
  have hfour : 4 ≤ Real.log X := by linarith [Real.log_two_gt_d9]
  have hlogn := Real.log_le_log hn hb
  rw [Real.log_pow] at hlogn
  have hnum : (7/2+(1+Real.log n)/2) ≤ 2*(1+Real.log X) := by norm_num at hlogn; linarith
  have hden : 0 < (5/2+2*(n:ℝ))-1 := by linarith
  have hfrac : 2/((5/2+2*(n:ℝ))-1) ≤ 1/(n:ℝ) := by
    apply (div_le_div_iff₀ hden hn).mpr; linarith
  have hln := Real.log_nonneg (show 1 ≤ (n:ℝ) by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hn.ne'))
  apply (mul_le_mul hfrac hnum (by linarith) (by positivity)).trans
  rw [one_div_mul_eq_div]
  apply (div_le_div_iff₀ hn (by positivity)).mpr
  nlinarith only [hnl, mul_nonneg hp.le (by linarith : 0 ≤ 1+Real.log X)]


theorem solution (N : ℕ) (hN : 196 ≤ N) :
    let X := (N:ℝ)
    let n := ⌈256*X^(3/2:ℝ)*(1+Real.log X)⌉₊
    let H := (5/2:ℝ)+2*(n:ℝ)
    (∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ H → z.val.re = 1/2) →
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z, z ∈ F ↔ |z.val.im| ≤ H) ∧ (∀ z ∈ F, z.val.re = 1/2) ∧
      Real.log 2/2 + Real.pi/4 - 37/30 +
        (∑ j ∈ Finset.range N, (vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
        ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4))) := by
  let n := ⌈256*(N:ℝ)^(3/2:ℝ)*(1+Real.log N)⌉₊
  change (∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ _ → z.val.re = 1/2) → _
  intro cover
  apply bounded_witness n N (Finset.Ioc N (4*N))
  · intro p hp; have := (Finset.mem_Ioc.mp hp).1; omega
  · exact cover
  · have hb := budget_for_height (N:ℝ) (by exact_mod_cast hN)
    change 2/((5/2+2*(n:ℝ))-1)*(7/2+(1+Real.log n)/2) ≤ _ at hb
    apply le_trans _ (hb.trans (prime_tail_reserve_to_four_mul N hN))
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
    linarith only [reference_bound]
