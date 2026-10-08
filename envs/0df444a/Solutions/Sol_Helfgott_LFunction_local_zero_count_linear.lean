-- Prove2me | solution 1 for Helfgott.LFunction_local_zero_count_linear
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T14:45:18.870024+00:00
-- url     : https://prove2.me/submissions/e453833a-58de-4697-8480-106cf6734896

import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Complex.JensenFormula

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Complex

namespace Helfgott

lemma rpow_strip_endpoint_bound (t a b σ : ℝ) (ht : 0 < t)
    (ha : a ≤ σ) (hb : σ ≤ b) :
    t^(σ-1) ≤ t^(a-1)+t^(b-1) := by
  by_cases h1 : 1 ≤ t
  · exact (Real.rpow_le_rpow_of_exponent_le h1 (by linarith : σ-1 ≤ b-1)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge ht (le_of_not_ge h1)
      (by linarith : a-1 ≤ σ-1)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))

theorem weakFEPair_entire_uniform_strip_bound (P : WeakFEPair ℂ) (a b : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ s : ℂ,a ≤ s.re → s.re ≤ b → ‖P.Λ₀ s‖ ≤ C := by
  let g : ℝ → ℝ := fun t => ‖(t : ℂ)^((a : ℂ)-1)*P.f_modif t‖+
    ‖(t : ℂ)^((b : ℂ)-1)*P.f_modif t‖
  have hc (s : ℂ) : IntegrableOn (fun t : ℝ => (t : ℂ)^(s-1)*P.f_modif t) (Ioi 0) := by
    simpa only [MellinConvergent,WeakFEPair.toStrongFEPair,smul_eq_mul] using
      (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  have hg : IntegrableOn g (Ioi 0) := (hc (a : ℂ)).norm.add (hc (b : ℂ)).norm
  refine ⟨∫ t : ℝ in Ioi 0,g t,integral_nonneg (fun t => add_nonneg (norm_nonneg _) (norm_nonneg _)),?_⟩
  intro s ha hb
  calc
    ‖P.Λ₀ s‖ ≤ ∫ t : ℝ in Ioi 0,‖(t : ℂ)^(s-1)*P.f_modif t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 0,g t := by
      apply integral_mono_ae (hc s).norm hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [g,norm_mul,norm_cpow_eq_rpow_re_of_pos ht,sub_re,ofReal_re,one_re]
      have h := rpow_strip_endpoint_bound t a b s.re ht ha hb
      nlinarith [norm_nonneg (P.f_modif t)]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Complex

namespace Helfgott

lemma completedHurwitzEven_entire_strip_bound (j : UnitAddCircle) (a b : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ s : ℂ,a ≤ s.re → s.re ≤ b →
      ‖HurwitzZeta.completedHurwitzZetaEven₀ j s‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := weakFEPair_entire_uniform_strip_bound (HurwitzZeta.hurwitzEvenFEPair j) (a/2) (b/2)
  refine ⟨C/2,by positivity,?_⟩
  intro s ha hb'
  have hh := hb (s/2) (by simp only [div_ofNat_re]; linarith) (by simp only [div_ofNat_re]; linarith)
  simpa only [HurwitzZeta.completedHurwitzZetaEven₀,norm_div,norm_ofNat] using (div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2))

lemma completedHurwitzOdd_strip_bound (j : UnitAddCircle) (a b : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ s : ℂ,a ≤ s.re → s.re ≤ b →
      ‖HurwitzZeta.completedHurwitzZetaOdd j s‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := weakFEPair_entire_uniform_strip_bound (HurwitzZeta.hurwitzOddFEPair j) ((a+1)/2) ((b+1)/2)
  refine ⟨C/2,by positivity,?_⟩
  intro s ha hb'
  have hh := hb ((s+1)/2) (by simp only [div_ofNat_re,add_re,one_re]; linarith)
    (by simp only [div_ofNat_re,add_re,one_re]; linarith)
  have he : (HurwitzZeta.hurwitzOddFEPair j).Λ ((s+1)/2)=
      (HurwitzZeta.hurwitzOddFEPair j).Λ₀ ((s+1)/2) := by
    simp [WeakFEPair.Λ,HurwitzZeta.hurwitzOddFEPair]
  simpa only [HurwitzZeta.completedHurwitzZetaOdd,he,norm_div,norm_ofNat] using
    (div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2))

theorem completed_LFunction_uniform_strip_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a b : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ s : ℂ,a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖χ.completedLFunction s‖ ≤ C := by
  classical
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqp : 0 < (q : ℝ) := zero_lt_one.trans_le hq
  choose Ce hCe hbe using fun j : ZMod q => completedHurwitzEven_entire_strip_bound (ZMod.toAddCircle j) a b
  choose Co hCo hbo using fun j : ZMod q => completedHurwitzOdd_strip_bound (ZMod.toAddCircle j) a b
  let A : ℝ := ∑ j : ZMod q,‖χ j‖*(Ce j+Co j)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (add_nonneg (hCe j) (hCo j)))
  refine ⟨(q : ℝ)^(-a)*(A+‖χ 0‖+‖∑ j : ZMod q,χ j‖),by positivity,?_⟩
  intro s ha hb ht
  have hn : ‖(q : ℂ)^(-s)‖ ≤ (q : ℝ)^(-a) := by
    rw [show (q : ℂ)=((q : ℝ) : ℂ) by norm_cast,norm_cpow_eq_rpow_re_of_pos hqp,neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have he : ‖∑ j : ZMod q,χ j*HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤
      ∑ j : ZMod q,‖χ j‖*Ce j := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbe j s ha hb) (norm_nonneg _)
  have ho : ‖∑ j : ZMod q,χ j*HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤
      ∑ j : ZMod q,‖χ j‖*Co j := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbo j s ha hb) (norm_nonneg _)
  have hs : 1 ≤ ‖s‖ := ht.trans (Complex.abs_im_le_norm s)
  have hs1 : 1 ≤ ‖1-s‖ := by
    have hh := Complex.abs_im_le_norm (1-s)
    simp only [sub_im,one_im,zero_sub,abs_neg] at hh
    exact ht.trans hh
  have h0 : ‖ZMod.completedLFunction₀ χ s‖ ≤ (q : ℝ)^(-a)*A := by
    rw [ZMod.completedLFunction₀]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul]
    have he' := mul_le_mul hn he (norm_nonneg _) (Real.rpow_nonneg hqp.le _)
    have ho' := mul_le_mul hn ho (norm_nonneg _) (Real.rpow_nonneg hqp.le _)
    have hh := add_le_add he' ho'
    convert hh using 1
    dsimp [A]
    simp_rw [mul_add,Finset.sum_add_distrib]
    ring
  change ‖ZMod.completedLFunction χ s‖ ≤ _
  rw [ZMod.completedLFunction_eq]
  calc
    _ ≤ ‖ZMod.completedLFunction₀ χ s‖+‖(q : ℂ)^(-s)*χ 0/s‖+
        ‖(q : ℂ)^(-s)*(∑ j : ZMod q,χ j)/(1-s)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (q : ℝ)^(-a)*A+(q : ℝ)^(-a)*‖χ 0‖+(q : ℝ)^(-a)*‖∑ j : ZMod q,χ j‖ := by
      refine add_le_add (add_le_add h0 ?_) ?_
      · rw [norm_div,norm_mul]
        exact (div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs).trans
          (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
      · rw [norm_div,norm_mul]
        exact (div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs1).trans
          (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    _ = _ := by ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Complex

namespace Helfgott

lemma complex_sin_exponential_bound (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have hh := congrArg norm (Complex.two_sin (x:=z))
  simp only [norm_mul,norm_ofNat,norm_I,mul_one] at hh
  have h1 : ‖Complex.exp (-z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [mul_re,neg_re,neg_im,I_re,I_im,mul_zero,mul_one,sub_self,zero_sub,neg_neg]
    exact le_abs_self _
  have h2 : ‖Complex.exp (z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [mul_re,I_re,I_im,mul_zero,mul_one,zero_sub]
    exact neg_le_abs _
  have ht := (norm_sub_le (Complex.exp (-z*I)) (Complex.exp (z*I))).trans (add_le_add h1 h2)
  linarith

lemma Gamma_positive_strip_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ z : ℂ,a ≤ z.re → z.re ≤ b → ‖Gamma z‖ ≤ C := by
  let g : ℝ → ℝ := fun t => Real.exp (-t)*(t^(a-1)+t^(b-1))
  by_cases hab : a ≤ b
  · have hb : 0 < b := ha.trans_le hab
    have hga := Real.GammaIntegral_convergent ha
    have hgb := Real.GammaIntegral_convergent hb
    have hg : IntegrableOn g (Ioi 0) := by
      convert! hga.add hgb using 1
      ext t
      simp only [g,mul_add,Pi.add_apply]
    have hgpos : 0 ≤ ∫ t : ℝ in Ioi 0,g t := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp [g]
      exact mul_nonneg (Real.exp_nonneg _) (add_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _))
    refine ⟨∫ t : ℝ in Ioi 0,g t,hgpos,?_⟩
    intro z haz hbz
    have hz : 0 < z.re := ha.trans_le haz
    rw [Complex.Gamma_eq_integral hz,Complex.GammaIntegral]
    refine (norm_integral_le_integral_norm _).trans ?_
    apply integral_mono_ae (Complex.GammaIntegral_convergent hz).norm hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [g,norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      norm_cpow_eq_rpow_re_of_pos ht,sub_re,one_re]
    exact mul_le_mul_of_nonneg_left (rpow_strip_endpoint_bound t a b z.re ht haz hbz) (Real.exp_nonneg _)
  · exact ⟨0,le_rfl,fun z haz hbz => False.elim (hab (haz.trans hbz))⟩

lemma Gamma_norm_le_shift_of_large_im (z : ℂ) (ht : 1 ≤ |z.im|) (n : ℕ) :
    ‖Gamma z‖ ≤ ‖Gamma (z+n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hti : 1 ≤ |(z+n).im| := by simpa using ht
    have hnorm : 1 ≤ ‖z+n‖ := hti.trans (Complex.abs_im_le_norm _)
    have hne : z+n ≠ 0 := by intro he; rw [he] at hnorm; norm_num at hnorm
    calc
      ‖Gamma z‖ ≤ ‖Gamma (z+n)‖ := ih
      _ ≤ ‖z+n‖*‖Gamma (z+n)‖ := le_mul_of_one_le_left (norm_nonneg _) hnorm
      _ = ‖Gamma (z+(n+1 : ℕ))‖ := by
        rw [← norm_mul,← Gamma_add_one _ hne]
        congr 2
        push_cast
        ring

theorem Gamma_inverse_uniform_strip_bound (a b : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ z : ℂ,a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖(Gamma z)⁻¹‖ ≤ C*Real.exp (Real.pi*|z.im|) := by
  obtain ⟨n,hn⟩ := exists_nat_gt b
  have hpos : 0 < 1-b+(n : ℝ) := by linarith
  obtain ⟨C,hC,hbound⟩ := Gamma_positive_strip_bound (1-b+n) (1-a+n) hpos
  refine ⟨C/Real.pi,by positivity,?_⟩
  intro z ha hb ht
  have hti : 1 ≤ |(1-z).im| := by simpa only [sub_im,one_im,zero_sub,abs_neg] using ht
  have hgb : ‖Gamma (1-z)‖ ≤ C :=
    (Gamma_norm_le_shift_of_large_im (1-z) hti n).trans
      (hbound (1-z+n) (by simp only [add_re,sub_re,one_re,natCast_re]; linarith)
        (by simp only [add_re,sub_re,one_re,natCast_re]; linarith))
  have hgz : Gamma z ≠ 0 := by
    apply Gamma_ne_zero
    intro m he
    have hh := congrArg Complex.im he
    simp only [neg_im,natCast_im,neg_zero] at hh
    rw [hh] at ht
    norm_num at ht
  have hsin : Complex.sin ((Real.pi : ℂ)*z) ≠ 0 := by
    have he := Gamma_mul_Gamma_one_sub z
    intro hz
    rw [hz,div_zero] at he
    have hgr : Gamma (1-z) ≠ 0 := by
      apply Gamma_ne_zero
      intro m hm
      have hh := congrArg Complex.im hm
      simp only [sub_im,one_im,zero_sub,neg_im,natCast_im,neg_zero,neg_eq_zero] at hh
      rw [hh] at ht
      norm_num at ht
    exact mul_ne_zero hgz hgr he
  have hid : (Gamma z)⁻¹=Gamma (1-z)*Complex.sin ((Real.pi : ℂ)*z)/(Real.pi : ℂ) := by
    have he := (eq_div_iff hsin).mp (Gamma_mul_Gamma_one_sub z)
    field_simp [hgz,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    simp_rw [mul_comm (Real.pi : ℂ) z] at he ⊢
    linear_combination -he
  have hs := complex_sin_exponential_bound ((Real.pi : ℂ)*z)
  simp only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,abs_mul,
    abs_of_pos Real.pi_pos] at hs
  rw [hid,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ C*Real.exp (Real.pi*|z.im|)/Real.pi := by gcongr
    _ = _ := by ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Complex

namespace Helfgott

lemma GammaR_inverse_uniform_strip_bound (a b : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ z : ℂ,a ≤ z.re → z.re ≤ b → 2 ≤ |z.im| →
      ‖(Gammaℝ z)⁻¹‖ ≤ C*Real.exp (Real.pi*|z.im|/2) := by
  obtain ⟨C,hC,hb⟩ := Gamma_inverse_uniform_strip_bound (a/2) (b/2)
  refine ⟨Real.pi^(b/2)*C,by positivity,?_⟩
  intro z ha hb' ht
  have hg := hb (z/2) (by simp only [div_ofNat_re]; linarith)
    (by simp only [div_ofNat_re]; linarith) (by simp only [div_ofNat_im,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]; linarith)
  have hp : ‖((Real.pi : ℂ)^(-z/2))⁻¹‖ ≤ Real.pi^(b/2) := by
    rw [norm_inv,norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp only [div_ofNat_re,neg_re]
    rw [← Real.rpow_neg Real.pi_pos.le]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.one_le_pi_div_two] : (1 : ℝ) ≤ Real.pi)
    linarith
  rw [Gammaℝ_def,mul_inv,norm_mul]
  have he : Real.pi*|(z/2).im|=Real.pi*|z.im|/2 := by simp [abs_div]; ring
  rw [he] at hg
  exact (mul_le_mul hp hg (norm_nonneg _) (by positivity)).trans_eq (by ring)

lemma gammaFactor_inverse_uniform_strip_bound (q : ℕ) (χ : DirichletCharacter ℂ q) (a b : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ z : ℂ,a ≤ z.re → z.re ≤ b → 2 ≤ |z.im| →
      ‖(χ.gammaFactor z)⁻¹‖ ≤ C*Real.exp (Real.pi*|z.im|/2) := by
  obtain ⟨C,hC,hb⟩ := GammaR_inverse_uniform_strip_bound a (b+1)
  refine ⟨C,hC,?_⟩
  intro z ha hb' ht
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact hb z ha (by linarith) ht
  · rw [ho.gammaFactor_def]
    simpa only [add_im,one_im,add_zero] using hb (z+1)
      (by simp only [add_re,one_re]; linarith)
      (by simp only [add_re,one_re]; linarith) (by simpa using ht)

theorem LFunction_uniform_strip_exponential_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a b : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ s : ℂ,a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| →
      ‖χ.LFunction s‖ ≤ C*Real.exp (Real.pi*|s.im|/2) := by
  obtain ⟨A,hA,hb⟩ := completed_LFunction_uniform_strip_bound q χ a b
  obtain ⟨B,hB,hg⟩ := gammaFactor_inverse_uniform_strip_bound q χ a b
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro s ha hb' ht
  have hs0 : s ≠ 0 := by intro he; rw [he] at ht; norm_num at ht
  rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0),div_eq_mul_inv,norm_mul]
  exact (mul_le_mul (hb s ha hb' (by linarith)) (hg s ha hb' ht) (norm_nonneg _) hA).trans_eq (by ring)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Complex

namespace Helfgott

lemma tsum_nat_rpow_five_quarters_le : (∑' n : ℕ,(n : ℝ)^(-(5/4 : ℝ))) ≤ 5 := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-(5/4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have ha : AntitoneOn (fun x : ℝ => x^(-(5/4 : ℝ))) (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : -(5/4 : ℝ) ≤ 0)).mono
      (by intro x hx; exact lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ x from hx))
  have ht := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using ha)
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(5/4 : ℝ)< -1) (by norm_num))
    (fun x hx => Real.rpow_nonneg (le_of_lt (show (0 : ℝ)<x from by
      have hx' : ((1 : ℕ) : ℝ)<x := hx
      norm_num at hx'
      linarith)) _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(5/4 : ℝ)< -1) (by norm_num)] at ht
  norm_num at ht
  have hs1 : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-(5/4 : ℝ))) :=
    (summable_nat_add_iff 1).mpr hs
  rw [hs.tsum_eq_zero_add,hs1.tsum_eq_zero_add]
  norm_num
  linarith [ht]

lemma dirichlet_prime_term_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 3/2 ≤ s.re) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ => χ m*(ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ ≤
      4*(n : ℝ)^(-(5/4 : ℝ)) := by
  by_cases hn : n=0
  · subst n
    simp
  have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hv : ArithmeticFunction.vonMangoldt n ≤ 4*(n : ℝ)^(1/4 : ℝ) := by
    have hl := Real.log_le_rpow_div hp.le (by norm_num : (0 : ℝ)<1/4)
    exact ArithmeticFunction.vonMangoldt_le_log.trans (by nlinarith [hl])
  rw [LSeries.norm_term_eq,if_neg hn,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc
    _ ≤ (1*(4*(n : ℝ)^(1/4 : ℝ)))/(n : ℝ)^s.re := by
      gcongr
      exact χ.norm_le_one n
    _ ≤ (4*(n : ℝ)^(1/4 : ℝ))/(n : ℝ)^(3/2 : ℝ) := by
      simp only [one_mul]
      gcongr
    _ = _ := by
      rw [mul_div_assoc,← Real.rpow_sub hp]
      norm_num

theorem dirichlet_LFunction_right_logDeriv_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 3/2 ≤ s.re) :
    LSeriesSummable (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)) s ∧
      ‖-deriv χ.LFunction s/χ.LFunction s‖ ≤ 20 := by
  have hs1 : 1 < s.re := by linarith
  have hec : ((fun n : ℕ => χ n)*(fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)))=
      (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)) := by ext n; rfl
  have hsum : LSeriesSummable (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    simpa only [hec] using χ.LSeriesSummable_twist_vonMangoldt hs1
  refine ⟨hsum,?_⟩
  have hid := χ.LSeries_twist_vonMangoldt_eq hs1
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs1,← χ.LFunction_eq_LSeries hs1] at hid
  simp only [hec] at hid
  rw [← hid]
  change ‖∑' n : ℕ,LSeries.term (fun m : ℕ => χ m*(ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ ≤ 20
  calc
    _ ≤ ∑' n : ℕ,‖LSeries.term (fun m : ℕ => χ m*(ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ,4*(n : ℝ)^(-(5/4 : ℝ)) := by
      exact Summable.tsum_le_tsum (fun n => dirichlet_prime_term_bound q χ s hs n)
        hsum.norm ((Real.summable_nat_rpow.mpr (by norm_num : -(5/4 : ℝ)< -1)).mul_left 4)
    _ ≤ 20 := by
      rw [tsum_mul_left]
      linarith [tsum_nat_rpow_five_quarters_le]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Complex
open scoped ArithmeticFunction.Moebius

namespace Helfgott

lemma tsum_nat_inverse_square_le_two : (∑' n : ℕ,(n : ℝ)^(-(2 : ℝ))) ≤ 2 := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-(2 : ℝ))) := Real.summable_nat_rpow.mpr (by norm_num)
  have ha : AntitoneOn (fun x : ℝ => x^(-(2 : ℝ))) (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : -(2 : ℝ) ≤ 0)).mono
      (by intro x hx; exact lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ x from hx))
  have ht := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using ha)
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ)< -1) (by norm_num))
    (fun x hx => Real.rpow_nonneg (le_of_lt (show (0 : ℝ)<x from by
      have hx' : ((1 : ℕ) : ℝ)<x := hx
      norm_num at hx'
      linarith)) _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ)< -1) (by norm_num)] at ht
  norm_num at ht
  have hs1 : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-(2 : ℝ))) := (summable_nat_add_iff 1).mpr hs
  rw [hs.tsum_eq_zero_add,hs1.tsum_eq_zero_add]
  norm_num
  linarith [ht]

lemma bounded_LSeries_right_norm_le_two (f : ℕ → ℂ) (hf : ∀ n : ℕ,‖f n‖ ≤ 1)
    (s : ℂ) (hs : 2 ≤ s.re) : ‖LSeries f s‖ ≤ 2 := by
  have hs1 : 1 < s.re := by linarith
  have hsum := LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) hs1
  have hn (n : ℕ) : ‖LSeries.term f s n‖ ≤ (n : ℝ)^(-(2 : ℝ)) := by
    by_cases hn : n=0
    · subst n; simp
    have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    rw [LSeries.norm_term_eq,if_neg hn]
    calc
      _ ≤ 1/(n : ℝ)^s.re := div_le_div_of_nonneg_right (hf n) (Real.rpow_nonneg hp.le _)
      _ ≤ 1/(n : ℝ)^(2 : ℝ) := by gcongr
      _ = _ := by rw [Real.rpow_neg hp.le,one_div]
  change ‖∑' n : ℕ,LSeries.term f s n‖ ≤ 2
  exact ((norm_tsum_le_tsum_norm hsum.norm).trans (Summable.tsum_le_tsum hn hsum.norm
    (Real.summable_nat_rpow.mpr (by norm_num : -(2 : ℝ)< -1)))).trans tsum_nat_inverse_square_le_two

theorem LFunction_right_anchor_lower_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 2 ≤ s.re) : (1/2 : ℝ) ≤ ‖χ.LFunction s‖ := by
  have hs1 : 1 < s.re := by linarith
  have hf (n : ℕ) : ‖(χ n)*(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      norm_cast
      exact ArithmeticFunction.abs_moebius_le_one
    rw [norm_mul]
    exact (mul_le_mul (χ.norm_le_one n) hμ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
  have hbound := bounded_LSeries_right_norm_le_two (fun n : ℕ => χ n*(ArithmeticFunction.moebius n : ℂ)) hf s hs
  have hid := congrArg norm (DirichletCharacter.LSeries.mul_mu_eq_one χ hs1)
  simp only [norm_mul,norm_one] at hid
  have he : ((fun n : ℕ => χ n)*(fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)))=
      (fun n : ℕ => χ n*(ArithmeticFunction.moebius n : ℂ)) := by ext n; rfl
  rw [he] at hid
  rw [χ.LFunction_eq_LSeries hs1]
  nlinarith [norm_nonneg (LSeries (fun n : ℕ => χ n) s)]

end Helfgott
end

section
set_option autoImplicit false
open Complex

namespace Helfgott

theorem LFunction_contour_growth_inputs (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a b : ℝ) :
    (∀ s : ℂ,2 ≤ s.re → (1/2 : ℝ) ≤ ‖χ.LFunction s‖) ∧
    ∃ C : ℝ,0 ≤ C ∧ ∀ s : ℂ,a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| →
      ‖χ.LFunction s‖ ≤ C*Real.exp (Real.pi*|s.im|/2) := by
  exact ⟨fun s hs => LFunction_right_anchor_lower_bound q χ s hs,
    LFunction_uniform_strip_exponential_bound q χ a b⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Metric Set Filter MeromorphicOn
open scoped Topology

namespace Helfgott

lemma vertical_disk_coordinates (T R : ℝ) (z : ℂ)
    (hz : z ∈ closedBall ((2 : ℂ)+(T : ℂ)*I) R) :
    2-R ≤ z.re ∧ z.re ≤ 2+R ∧ T-R ≤ z.im ∧ z.im ≤ T+R := by
  have hnorm : ‖z-((2 : ℂ)+(T : ℂ)*I)‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hr := (Complex.abs_re_le_norm (z-((2 : ℂ)+(T : ℂ)*I))).trans hnorm
  have hi := (Complex.abs_im_le_norm (z-((2 : ℂ)+(T : ℂ)*I))).trans hnorm
  simp at hr hi
  obtain ⟨hrl,hru⟩ := abs_le.mp hr
  obtain ⟨hil,hiu⟩ := abs_le.mp hi
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma LFunction_analyticOnNhd_off_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro z hz
  exact (χ.differentiableAt_LFunction z (.inl hz)).differentiableWithinAt

theorem LFunction_local_zero_count_linear (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ T : ℝ,8 ≤ T →
      ((∑ᶠ z : ℂ,divisor χ.LFunction (closedBall ((2 : ℂ)+(T : ℂ)*I) 4) z : ℤ) : ℝ) ≤ K*(1+T) := by
  obtain ⟨C,hC,hgrowth⟩ := LFunction_uniform_strip_exponential_bound q χ (-3) 7
  let A : ℝ := max C 1
  have hA : 1 ≤ A := le_max_right _ _
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hlogA : 0 ≤ Real.log (2*A) := Real.log_nonneg (by linarith)
  have hden : 0 < Real.log ((5 : ℝ)/4) := Real.log_pos (by norm_num)
  let K : ℝ := (Real.log (2*A)+3*Real.pi)/Real.log ((5 : ℝ)/4)
  have hK : 0 ≤ K := div_nonneg (add_nonneg hlogA (by positivity)) hden.le
  refine ⟨K,hK,?_⟩
  intro T hT
  let c : ℂ := (2 : ℂ)+(T : ℂ)*I
  let M : ℝ := A*Real.exp (Real.pi*(T+5)/2)
  have hM : 1 ≤ M := by
    have hex : 1 ≤ Real.exp (Real.pi*(T+5)/2) := Real.one_le_exp (by positivity)
    dsimp [M]
    nlinarith
  have hf : AnalyticOnNhd ℂ χ.LFunction (closedBall c 5) := by
    intro z hz
    have hc := vertical_disk_coordinates T 5 z hz
    apply LFunction_analyticOnNhd_off_one q χ z
    intro he
    subst z
    have hi := hc.2.2.1
    norm_num at hi
    linarith
  have hanchor : (1/2 : ℝ) ≤ ‖χ.LFunction c‖ :=
    LFunction_right_anchor_lower_bound q χ c (by simp [c])
  have hnon : χ.LFunction c ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖χ.LFunction c‖ ≠ 0)
  have hbound (z : ℂ) (hz : z ∈ sphere c 5) : ‖χ.LFunction z‖ ≤ M := by
    have hc := vertical_disk_coordinates T 5 z (sphere_subset_closedBall hz)
    have hzpos : 0 ≤ z.im := by linarith [hc.2.2.1]
    have hh := hgrowth z (by norm_num at hc ⊢; linarith [hc.1]) (by norm_num at hc ⊢; linarith [hc.2.1]) (by rw [abs_of_nonneg hzpos]; linarith [hc.2.2.1])
    refine hh.trans ?_
    dsimp [M]
    gcongr
    · exact le_max_left _ _
    · rw [abs_of_nonneg hzpos]
      exact hc.2.2.2
  have hj := AnalyticOnNhd.sum_divisor_le (by norm_num : 0 < |(4 : ℝ)|) (by norm_num : |(4 : ℝ)| < |(5 : ℝ)|) hM (by simpa using hf) hnon (by simpa using hbound)
  rw [show |(4 : ℝ)|=4 by norm_num] at hj
  refine hj.trans ?_
  have hn : 0 < ‖χ.LFunction c‖ := norm_pos_iff.mpr hnon
  have hratio : M/‖χ.LFunction c‖ ≤ 2*M := by
    apply (div_le_iff₀ hn).mpr
    nlinarith [show 0 ≤ M by linarith]
  have hlog : Real.log (M/‖χ.LFunction c‖) ≤ Real.log (2*A)+Real.pi*(T+5)/2 := by
    have hp : 0 < M/‖χ.LFunction c‖ := div_pos (by linarith) hn
    have hh := Real.log_le_log hp hratio
    have he : 2*M=(2*A)*Real.exp (Real.pi*(T+5)/2) := by dsimp [M]; ring
    rw [he,Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp] at hh
    exact hh
  have hnum : Real.log (M/‖χ.LFunction c‖) ≤ (Real.log (2*A)+3*Real.pi)*(1+T) := by
    nlinarith [Real.pi_pos,mul_nonneg hlogA (by linarith : 0 ≤ T)]
  have hh := div_le_div_of_nonneg_right hnum hden.le
  convert hh using 1
  dsimp [K]
  ring

end Helfgott
end

open Complex Metric Set Filter MeromorphicOn
open scoped Topology

theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ T : ℝ,8 ≤ T →
      ((∑ᶠ z : ℂ,divisor χ.LFunction (closedBall ((2 : ℂ)+(T : ℂ)*I) 4) z : ℤ) : ℝ) ≤ K*(1+T) := Helfgott.LFunction_local_zero_count_linear q χ

#print axioms solution
