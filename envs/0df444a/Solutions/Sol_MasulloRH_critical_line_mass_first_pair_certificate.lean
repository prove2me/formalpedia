-- Prove2me | solution 1 for MasulloRH.critical_line_mass_first_pair_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:58:37.290423+00:00
-- url     : https://prove2.me/submissions/5cd760ea-f5f1-43db-b84d-4666e82126c5

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_XiQuantitativePublished_zeta_zero_between_1413_1414
import Mathlib

open Set ArithmeticFunction
open MasulloRH

private theorem prime_term_bound {n : ℕ} {l U : ℝ} (hn : 1 ≤ n) (hl : 0 < l)
    (hsq : l^2 ≤ n) (hU : vonMangoldt n ≤ U) :
    vonMangoldt n / (n:ℝ)^(5/2:ℝ) - vonMangoldt n / (n:ℝ)^(3:ℝ) ≤
      U*(1/((n:ℝ)^2*l)-1/(n:ℝ)^3) := by
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hL : l ≤ Real.sqrt (n:ℝ) := (Real.le_sqrt hl.le (by positivity)).mpr hsq
  have hroot : Real.sqrt (n:ℝ) ≤ n := by
    apply (Real.sqrt_le_iff.mpr ⟨hn0.le,?_⟩)
    nlinarith [mul_nonneg hn0.le (show 0 ≤ (n:ℝ)-1 by linarith)]
  have hp := Real.rpow_add hn0 (2:ℝ) (1/2:ℝ)
  rw [show (2:ℝ)+1/2 = 5/2 by norm_num, Real.rpow_two, ← Real.sqrt_eq_rpow] at hp
  rw [hp,Real.rpow_ofNat]
  have hc : 0 ≤ 1 / ((n:ℝ)^2*Real.sqrt (n:ℝ)) - 1/(n:ℝ)^3 := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    simpa [pow_succ] using mul_le_mul_of_nonneg_left hroot (sq_nonneg (n:ℝ))
  have hK : 1/((n:ℝ)^2*Real.sqrt n) ≤ 1/((n:ℝ)^2*l) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hL (sq_nonneg _))
  calc _ = vonMangoldt n * (1 / ((n:ℝ)^2*Real.sqrt (n:ℝ)) - 1/(n:ℝ)^3) := by ring
       _ ≤ U*(1 / ((n:ℝ)^2*l)-1/(n:ℝ)^3) :=
         mul_le_mul hU (sub_le_sub_right hK _) hc (vonMangoldt_nonneg.trans hU)

private theorem finite_prime_target_le {N : ℕ} (hN : N ≤ 9) :
    Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑ n ∈ Finset.range N, (vonMangoldt n / (n:ℝ)^(5/2:ℝ) - vonMangoldt n / (n:ℝ)^(3:ℝ))) ≤
    23/5000 := by
  let f (n : ℕ) := vonMangoldt n / (n:ℝ)^(5/2:ℝ) - vonMangoldt n / (n:ℝ)^(3:ℝ)
  have hpos (n : ℕ) : 0 ≤ f n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f]
    have h1 : 1 ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left vonMangoldt_nonneg (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
    (fun n _ _ => hpos n)
  change _ + (∑ n ∈ Finset.range N, f n) ≤ _
  apply (add_le_add_right hle _).trans
  have h2 : vonMangoldt 2 ≤ (694/1000:ℝ) := by
    rw [vonMangoldt_apply_prime (by decide)]; linarith [Real.log_two_lt_d9]
  have h3 : vonMangoldt 3 ≤ (1099/1000:ℝ) := by
    rw [vonMangoldt_apply_prime (by decide)]; linarith [Real.log_three_lt_d9]
  have h4 : vonMangoldt 4 ≤ (694/1000:ℝ) := by
    change vonMangoldt (2^2) ≤ _; rwa [vonMangoldt_apply_pow (by decide)]
  have h5 : vonMangoldt 5 ≤ (161/100:ℝ) := by
    rw [vonMangoldt_apply_prime (by decide)]; linarith [Real.log_five_lt_d9]
  have h6 : vonMangoldt 6 = 0 := vonMangoldt_eq_zero_iff.mpr (by decide)
  have h7 : vonMangoldt 7 ≤ (2:ℝ) := by
    rw [vonMangoldt_apply_prime (by decide),Real.log_le_iff_le_exp (by norm_num),
      show (2:ℝ)=1+1 by norm_num,Real.exp_add]
    have hL : (2.7:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact (show (7:ℝ) ≤ 2.7*2.7 by norm_num).trans
      (mul_le_mul hL hL (by norm_num) (Real.exp_pos _).le)
  have h8 : vonMangoldt 8 ≤ (694/1000:ℝ) := by
    change vonMangoldt (2^3) ≤ _; rwa [vonMangoldt_apply_pow (by decide)]
  have b2 := prime_term_bound (n:=2) (l:=1.414) (by decide) (by norm_num) (by norm_num) h2
  have b3 := prime_term_bound (n:=3) (l:=1.732) (by decide) (by norm_num) (by norm_num) h3
  have b4 := prime_term_bound (n:=4) (l:=2) (by decide) (by norm_num) (by norm_num) h4
  have b5 := prime_term_bound (n:=5) (l:=2.236) (by decide) (by norm_num) (by norm_num) h5
  have b7 := prime_term_bound (n:=7) (l:=2.645) (by decide) (by norm_num) (by norm_num) h7
  have b8 := prime_term_bound (n:=8) (l:=2.828) (by decide) (by norm_num) (by norm_num) h8
  simp only [Finset.sum_range_succ,Finset.sum_range_zero] at *
  norm_num [f,h6] at b2 b3 b4 b5 b7 b8 ⊢
  linarith only [b2,b3,b4,b5,b7,b8,Real.pi_lt_d4,Real.log_two_lt_d9]

-- Positivity argument from Yi's proof of MasulloRH.single_resolvent_test.
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

private theorem one_ordinate_bound (z : ZetaZerosInTraceStrip (1/2))
    (hl : (1413/100:ℝ)^2 ≤ z.val.im^2) (hu : z.val.im^2 ≤ (707/50:ℝ)^2) :
    23/10000 ≤ (analyticOrderNatAt riemannZeta z.val:ℝ) *
      ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4))) := by
  let Y := z.val.im^2
  have hy0 : 0 ≤ Y := sq_nonneg _
  have hnum : (1413/100:ℝ)^2-5 ≤ Y-5 := sub_le_sub_right hl 5
  have hden : 2*(Y+25/4)*(Y+4) ≤ 2*((707/50:ℝ)^2+25/4)*((707/50:ℝ)^2+4) :=
    mul_le_mul (by linarith only [hu]) (by linarith only [hu]) (by positivity) (by norm_num)
  have hval : 23/10000 ≤ (Y-5)/(2*(Y+25/4)*(Y+4)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith only [hden,hnum]
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta z.val := by exact_mod_cast multiplicity_pos z
  exact hval.trans (le_mul_of_one_le_left (by linarith) hm)

theorem solution :
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)), F.card = 2 ∧
      (∀ z ∈ F, z.val.re = 1/2 ∧ 1413/100 < |z.val.im| ∧ |z.val.im| < 707/50) ∧
      23/5000 ≤ (∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))) ∧
      ∀ N : ℕ, N ≤ 9 → Real.log 2/2 + Real.pi/4 - 37/30 +
        (∑ n ∈ Finset.range N, (vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
          vonMangoldt n / (n:ℝ)^(3:ℝ))) ≤ 23/5000 := by
  classical
  obtain ⟨t,ht,hz⟩ := XiQuantitativePublished.zeta_zero_between_1413_1414
  have ht0 : 0 < t := by linarith [ht.1]
  let u : ℂ := 1/2+(t:ℂ)*Complex.I
  have hur : u.re = 1/2 := by norm_num [u,Complex.add_re,Complex.mul_re,Complex.div_ofNat_re]
  have hui : u.im = t := by norm_num [u,Complex.add_im,Complex.mul_im,Complex.div_ofNat_im]
  have hvr : (1-u).re = 1/2 := by rw [Complex.sub_re,Complex.one_re,hur]; ring
  have hvi : (1-u).im = -t := by simp [Complex.sub_im,hui]
  have hnot (n : ℕ) : u ≠ -n := by
    intro h; have he := congrArg Complex.re h; simp [hur] at he; linarith [n.cast_nonneg (α:=ℝ)]
  have h1 : u ≠ 1 := by intro h; have he := congrArg Complex.re h; norm_num [hur] at he
  have hz' : riemannZeta (1-u) = 0 := by rw [riemannZeta_one_sub hnot h1,show riemannZeta u = 0 from hz,mul_zero]
  let a : ZetaZerosInTraceStrip (1/2) := ⟨u,hz,by norm_num [hur],by norm_num [hur],by norm_num [hur]⟩
  let b : ZetaZerosInTraceStrip (1/2) := ⟨1-u,hz',by norm_num [hvr],by norm_num [hvr],by norm_num [hvr]⟩
  have hab : a ≠ b := by
    intro h; have he := congrArg (fun z : ZetaZerosInTraceStrip (1/2) => z.val.im) h
    change u.im = (1-u).im at he; rw [hui,hvi] at he; linarith
  have hL : (1413/100:ℝ)^2 ≤ t^2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤1413/100) ht.1.le]
  have hU : t^2 ≤ (707/50:ℝ)^2 := by nlinarith [mul_self_le_mul_self ht0.le ht.2.le]
  have ha := one_ordinate_bound a (by simpa [a,hui] using hL) (by simpa [a,hui] using hU)
  have hb := one_ordinate_bound b (by simpa [b,hvi] using hL) (by simpa [b,hvi] using hU)
  refine ⟨{a,b}, by simp [hab], ?_, ?_, fun N hN => finite_prime_target_le hN⟩
  · intro z hzF
    rcases Finset.mem_insert.mp hzF with rfl | hzF
    · simpa [a,hur,hui,abs_of_pos ht0] using ht
    · obtain rfl := Finset.mem_singleton.mp hzF
      simpa [b,hvr,hvi,abs_of_pos ht0] using ht
  · rw [Finset.sum_pair hab]
    linarith only [ha,hb]

