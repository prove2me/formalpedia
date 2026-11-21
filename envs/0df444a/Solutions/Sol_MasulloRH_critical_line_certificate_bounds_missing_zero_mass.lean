-- Prove2me | solution 1 for MasulloRH.critical_line_certificate_bounds_missing_zero_mass
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:56:39.34419+00:00
-- url     : https://prove2.me/submissions/06d27869-4a82-427d-9a36-be658261e3d5

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Mathlib

open Finset ArithmeticFunction Filter Topology
open MasulloRH
private theorem six_lt_ordinate (z : ZetaZerosInTraceStrip (1/2)) : 6 < |z.val.im| := by
  by_contra! h
  exact ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six z.prop.2.1 z.prop.2.2.1 h z.prop.1

private theorem kernel_dominates_weight {β γ : ℝ} (hβ : 0 < β) (h1 : β < 1) (hy : 6 < |γ|) :
    1 / (1+γ^2) ≤ 16 * ((3-β)/((3-β)^2+γ^2) - (5/2-β)/((5/2-β)^2+γ^2)) := by
  let a := 3-β
  let b := 5/2-β
  let Y := γ^2
  have hY : 36 ≤ Y := by dsimp [Y]; nlinarith [sq_abs γ,sq_nonneg (|γ|-6)]
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have ha3 : a ≤ 3 := by dsimp [a]; linarith
  have hb3 : b ≤ 3 := by dsimp [b]; linarith
  have hab : a*b ≤ 9 := by nlinarith [mul_le_mul ha3 hb3 hb (by norm_num : (0:ℝ)≤3)]
  have ha2 : a^2 ≤ 9 := by nlinarith [mul_le_mul ha3 ha3 ha (by norm_num : (0:ℝ)≤3)]
  have hb2 : b^2 ≤ 9 := by nlinarith [mul_le_mul hb3 hb3 hb (by norm_num : (0:ℝ)≤3)]
  have hA : 0 < a^2+Y := by nlinarith [sq_nonneg a]
  have hB : 0 < b^2+Y := by nlinarith [sq_nonneg b]
  have hden : (a^2+Y)*(b^2+Y) ≤ (2*Y)*(2*Y) :=
    mul_le_mul (by linarith) (by linarith) hB.le (by linarith)
  have hnum : (2*Y)*(2*Y) ≤ 8*(Y-a*b)*(1+Y) := by
    have h := mul_le_mul (show 4*Y ≤ 8*(Y-a*b) by linarith) (show Y ≤ 1+Y by linarith)
      (show 0 ≤ Y by linarith) (show 0 ≤ 8*(Y-a*b) by linarith)
    nlinarith
  change 1/(1+Y) ≤ 16*(a/(a^2+Y)-b/(b^2+Y))
  have e : 16*(a/(a^2+Y)-b/(b^2+Y)) = (8*(Y-a*b))/((a^2+Y)*(b^2+Y)) := by
    field_simp [hA.ne',hB.ne']
    dsimp [a,b]
    ring
  rw [e]
  exact (div_le_div_iff₀ (by linarith) (mul_pos hA hB)).mpr (by simpa using hden.trans hnum)

private theorem term_comparison (ρ : ZetaZerosInTraceStrip (1/2)) :
    zeroDecayWeight (1/2) ρ ≤ 16*(zeroResolventTerm (1/2) 3 ρ).re ∧
    ‖zeroResolventTerm (1/2) 3 ρ‖ ≤ zeroDecayWeight (1/2) ρ := by
  let z := ρ.val
  let m := analyticOrderNatAt riemannZeta z
  have hy : 6 < |z.im| := six_lt_ordinate ρ
  have hy2 : 1 ≤ z.im^2 := by nlinarith [sq_abs z.im,sq_nonneg (|z.im|-6)]
  constructor
  · have hk := kernel_dominates_weight ρ.prop.2.1 ρ.prop.2.2.1 hy
    have he : (1/(3-z)-1/(5/2-z)).re =
        (3-z.re)/((3-z.re)^2+z.im^2) - (5/2-z.re)/((5/2-z.re)^2+z.im^2) := by
      simp only [one_div,Complex.sub_re,Complex.inv_re,Complex.normSq_apply,Complex.sub_im]
      norm_num [pow_two,Complex.div_ofNat_re,Complex.div_ofNat_im]
    unfold zeroDecayWeight zeroResolventTerm
    change (m:ℝ)/(1+z.im^2) ≤ 16*(((m:ℂ)*(1/(3-z)-1/(5/2-z))).re)
    rw [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,he]
    calc _ = (m:ℝ)*(1/(1+z.im^2)) := by ring
         _ ≤ _ := (mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg m)).trans_eq (by ring)
  · have hx : |z.im| ≤ ‖3-z‖ := by simpa using Complex.abs_im_le_norm (3-z)
    have hb : |z.im| ≤ ‖5/2-z‖ := by simpa using Complex.abs_im_le_norm (5/2-z)
    have ha0 : 0 < ‖3-z‖ := by linarith
    have hb0 : 0 < ‖5/2-z‖ := by linarith
    have he : 1/(3-z)-1/(5/2-z) = (-1/2:ℂ)/((3-z)*(5/2-z)) := by
      have iden (a b:ℂ) (ha:a ≠ 0) (hb:b ≠ 0) : 1/a-1/b=(b-a)/(a*b) := by
        field_simp
      rw [iden _ _ (norm_pos_iff.mp ha0) (norm_pos_iff.mp hb0)]
      ring
    unfold zeroDecayWeight zeroResolventTerm
    change ‖(m:ℂ)*(1/(3-z)-1/(5/2-z))‖ ≤ (m:ℝ)/(1+z.im^2)
    rw [he,norm_mul,Complex.norm_natCast,div_eq_mul_one_div (m:ℝ)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
    rw [norm_div,norm_mul]
    have hn : ‖(-1/2:ℂ)‖ = 1/2 := by norm_num
    rw [hn,div_le_div_iff₀ (mul_pos ha0 hb0) (by positivity)]
    nlinarith [mul_le_mul hx hb (abs_nonneg z.im) ha0.le,sq_abs z.im]


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




private noncomputable def primeWeight (j : ℕ) : ℝ :=
  vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ)

private theorem pw_nonneg (j : ℕ) : 0 ≤ primeWeight j := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp [primeWeight]
  have h1 : 1 ≤ (j:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
  exact sub_nonneg.mpr (div_le_div_of_nonneg_left vonMangoldt_nonneg
    (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)))

private theorem dyadic_block (n : ℕ) (hn : 1 ≤ n) :
    (∑ j ∈ Ioc n (2*n), primeWeight j) ≤ 12/(n:ℝ)^(3/2:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hpsi := Chebyshev.psi_le_const_mul_self (by positivity : 0 ≤ ((2*n:ℕ):ℝ))
  rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow] at hpsi
  have hlog : (2:ℝ)*Real.log 2+4 ≤ 6 := by linarith [Real.log_two_lt_d9]
  have hsum : (∑ j ∈ Ioc n (2*n), vonMangoldt j) ≤ 12*(n:ℝ) := by
    calc _ ≤ Chebyshev.psi (2*n:ℕ) := by
            simp only [Chebyshev.psi,Nat.floor_natCast]
            apply sum_le_sum_of_subset_of_nonneg
            · intro j hj; obtain ⟨h,h'⟩ := mem_Ioc.mp hj; exact mem_Ioc.mpr ⟨by omega,h'⟩
            · intros; exact vonMangoldt_nonneg
         _ ≤ _ := by
            apply hpsi.trans
            push_cast
            have h := mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ 2*(n:ℝ))
            linarith
  calc _ ≤ ∑ j ∈ Ioc n (2*n), vonMangoldt j/(n:ℝ)^(5/2:ℝ) := by
          apply sum_le_sum
          intro j hj
          apply (sub_le_self _ (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg j.cast_nonneg _))).trans
          apply div_le_div_of_nonneg_left vonMangoldt_nonneg (Real.rpow_pos_of_pos hn' _)
          apply Real.rpow_le_rpow n.cast_nonneg _ (by norm_num)
          exact_mod_cast (mem_Ioc.mp hj).1.le
       _ ≤ (12*(n:ℝ))/(n:ℝ)^(5/2:ℝ) := by
          rw [←sum_div]; exact div_le_div_of_nonneg_right hsum (by positivity)
       _ = _ := by
          rw [show (5/2:ℝ)=3/2+1 by norm_num,Real.rpow_add_one hn'.ne']
          field_simp [hn'.ne']

private theorem dyadic_blocks (k n : ℕ) (hn : 1 ≤ n) :
    (∑ j ∈ Ioc n (2^k*n), primeWeight j) ≤ 24/(n:ℝ)^(3/2:ℝ) := by
  induction k generalizing n with
  | zero => simp; positivity
  | succ k ih =>
    have h2 : 2*n ≤ 2^k*(2*n) := Nat.le_mul_of_pos_left _ (by positivity)
    rw [pow_succ,Nat.mul_assoc,←Finset.Ioc_union_Ioc_eq_Ioc (show n ≤ 2*n by omega) h2,
      Finset.sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
    apply (add_le_add (dyadic_block n hn) (ih (2*n) (by omega))).trans
    have hn' : (0:ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    push_cast
    rw [Real.mul_rpow (by norm_num) hn'.le]
    have htwo : (2:ℝ) ≤ (2:ℝ)^(3/2:ℝ) := by
      conv_lhs => rw [←Real.rpow_one (2:ℝ)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hle : 24 / ((2:ℝ)^(3/2:ℝ)*(n:ℝ)^(3/2:ℝ)) ≤ 24 / (2*(n:ℝ)^(3/2:ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right htwo (by positivity))
    linarith only [hle,show 24 / (2*(n:ℝ)^(3/2:ℝ)) = 12/(n:ℝ)^(3/2:ℝ) by ring,
      show 24/(n:ℝ)^(3/2:ℝ) = 2*(12/(n:ℝ)^(3/2:ℝ)) by ring]

private theorem bound_complete_sum {S : ℝ} (hS : HasSum primeWeight S) (n : ℕ) (hn : 1 ≤ n) :
    S ≤ (∑ j ∈ range (n+1), primeWeight j) + 24/(n:ℝ)^(3/2:ℝ) := by
  apply le_of_tendsto hS.tendsto_sum_nat (Eventually.of_forall _)
  intro m
  have hmn : m ≤ 2^m*n := m.lt_two_pow_self.le.trans <| Nat.le_mul_of_pos_right _ (by omega)
  have hb : (∑ j ∈ range m, primeWeight j) ≤ ∑ j ∈ range (2^m*n+1), primeWeight j :=
    sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ_of_le hmn)) (fun j _ _ => pw_nonneg j)
  apply hb.trans
  have he : range (2^m*n+1) = range (n+1) ∪ Ioc n (2^m*n) := by
    have h : n ≤ 2^m*n := Nat.le_mul_of_pos_left _ (by positivity)
    ext j; simp; omega
  have hdis : Disjoint (range (n+1)) (Ioc n (2^m*n)) := disjoint_left.mpr (by
    intro j hj hk; have := mem_range.mp hj; have := (mem_Ioc.mp hk).1; omega)
  rw [he,sum_union hdis]
  exact add_le_add (le_refl _) (dyadic_blocks m n hn)


theorem solution (N : ℕ) (hN : 1 ≤ N)
    (F : Finset (ZetaZerosInTraceStrip (1/2))) (hF : ∀ z ∈ F, z.val.re = 1/2)
    (hcert : Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑ j ∈ Finset.range (N+1), (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))) :
    (∑' z : ZetaZerosInTraceStrip (1/2), if z ∈ F then 0 else zeroDecayWeight (1/2) z)
         ≤ 384/(N:ℝ)^(3/2:ℝ) ∧
    ∀ z : ZetaZerosInTraceStrip (1/2), z ∉ F →
      (analyticOrderNatAt riemannZeta z.val:ℝ)*(N:ℝ)^(3/2:ℝ) ≤ 384*(1+z.val.im^2) := by
  classical
  let Z := ZetaZerosInTraceStrip (1/2)
  let w := zeroDecayWeight (1/2)
  let r := zeroResolventTerm (1/2) 3
  let k (z : Z) := (r z).re
  let A := (zetaLogDeriv 3).re-(zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re
  let C := Real.log 2/2 + Real.pi/4 - 37/30
  have hw : Summable w := weighted_zero_summability _ (by norm_num)
  have hr : Summable r := hw.of_norm_bounded (fun z => (term_comparison z).2)
  have hk : Summable k := (Complex.hasSum_re hr.hasSum).summable
  have hw0 (z : Z) : 0 ≤ w z := by dsimp [w,zeroDecayWeight]; positivity
  have hwk (z : Z) : w z ≤ 16*k z := (term_comparison z).1
  have hsum : A = ∑' z,k z := by
    dsimp only [A]
    rw [←regularized_initial_identity_full_strip (3:ℂ) (by norm_num)]
    change (_ + ∑' z,r z).re - _ = _
    rw [Complex.add_re,add_sub_cancel_left,Complex.re_tsum hr]
  let O : Set Z := (F : Set Z)ᶜ
  have hsplit : (∑ z ∈ F,k z)+(∑' z,O.indicator k z) = A := by
    rw [hsum,←_root_.tsum_subtype]
    exact hk.sum_add_tsum_compl (s:=F)
  have hcond : C + (∑ j ∈ range (N+1),primeWeight j) ≤ ∑ z ∈ F,k z := by
    apply hcert.trans_eq
    apply sum_congr rfl
    intro z hz
    exact (line_kernel z (hF z hz)).symm
  have hprime : HasSum primeWeight (A-C) := by
    convert regularized_reference_mass_prime_series using 1
    · rfl
    · dsimp [A,C]; ring
  have htotal := bound_complete_sum hprime N hN
  have hrem : (∑' z,O.indicator k z) ≤ 24/(N:ℝ)^(3/2:ℝ) := by linarith only [hsplit,hcond,htotal]
  have hbound : (∑' z, O.indicator w z) ≤ 384/(N:ℝ)^(3/2:ℝ) := by
    calc _ ≤ ∑' z,16*O.indicator k z := by
            apply (hw.indicator O).tsum_le_tsum _ ((hk.indicator O).mul_left 16)
            intro z
            by_cases ho : z ∈ O
            · rw [Set.indicator_of_mem ho,Set.indicator_of_mem ho]; exact hwk z
            · simp [Set.indicator_of_notMem ho]
         _ = 16*∑' z,O.indicator k z := tsum_mul_left
         _ ≤ 16*(24/(N:ℝ)^(3/2:ℝ)) := mul_le_mul_of_nonneg_left hrem (by norm_num)
         _ = _ := by ring
  constructor
  · simpa only [O,Set.indicator_apply,Set.mem_compl_iff,Finset.mem_coe,ite_not,w] using hbound
  · intro z hz
    have ho : z ∈ O := hz
    have hsingle : w z ≤ ∑' x,O.indicator w x := by
      have h := (hw.indicator O).le_tsum z (fun x _ => Set.indicator_nonneg (fun y _ => hw0 y) x)
      rw [Set.indicator_of_mem ho] at h
      exact h
    have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    exact (div_le_div_iff₀ (by positivity) (Real.rpow_pos_of_pos hn _)).mp (hsingle.trans hbound)

