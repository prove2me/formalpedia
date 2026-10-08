-- Prove2me | solution 1 for Helfgott.LFunction_selected_horizontal_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T15:12:08.51382+00:00
-- url     : https://prove2.me/submissions/5a32a17c-6fba-4128-8781-4d62b21f7bf5

import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Metric Set Filter MeromorphicOn
open scoped Topology

namespace Helfgott

lemma vertical_disk_im_abs_bounds (T R : ℝ) (z : ℂ)
    (hz : z ∈ closedBall ((2 : ℂ)+(T : ℂ)*I) R) :
    |T|-R ≤ |z.im| ∧ |z.im| ≤ |T|+R := by
  have hnorm : ‖z-((2 : ℂ)+(T : ℂ)*I)‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hi := (Complex.abs_im_le_norm (z-((2 : ℂ)+(T : ℂ)*I))).trans hnorm
  simp at hi
  have h1 := norm_le_norm_sub_add z.im T
  have h2 := norm_le_norm_sub_add T z.im
  simp only [Real.norm_eq_abs,abs_sub_comm T z.im] at h1 h2
  constructor <;> linarith

theorem LFunction_local_zero_count_linear_both (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ T : ℝ,8 ≤ |T| →
      ((∑ᶠ z : ℂ,divisor χ.LFunction (closedBall ((2 : ℂ)+(T : ℂ)*I) 4) z : ℤ) : ℝ) ≤ K*(1+|T|) := by
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
  let M : ℝ := A*Real.exp (Real.pi*(|T|+5)/2)
  have hM : 1 ≤ M := by
    have hex : 1 ≤ Real.exp (Real.pi*(|T|+5)/2) := Real.one_le_exp (by positivity)
    dsimp [M]
    nlinarith
  have hf : AnalyticOnNhd ℂ χ.LFunction (closedBall c 5) := by
    intro z hz
    have hi := (vertical_disk_im_abs_bounds T 5 z hz).1
    apply LFunction_analyticOnNhd_off_one q χ z
    intro he
    subst z
    norm_num at hi
    linarith
  have hanchor : (1/2 : ℝ) ≤ ‖χ.LFunction c‖ :=
    LFunction_right_anchor_lower_bound q χ c (by simp [c])
  have hnon : χ.LFunction c ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖χ.LFunction c‖ ≠ 0)
  have hbound (z : ℂ) (hz : z ∈ sphere c 5) : ‖χ.LFunction z‖ ≤ M := by
    have hc := vertical_disk_coordinates T 5 z (sphere_subset_closedBall hz)
    have hi := vertical_disk_im_abs_bounds T 5 z (sphere_subset_closedBall hz)
    have hh := hgrowth z (by norm_num at hc ⊢; linarith [hc.1])
      (by norm_num at hc ⊢; linarith [hc.2.1]) (by linarith [hi.1])
    refine hh.trans ?_
    dsimp [M]
    gcongr
    · exact le_max_left _ _
    · exact hi.2
  have hj := AnalyticOnNhd.sum_divisor_le (by norm_num : 0 < |(4 : ℝ)|) (by norm_num : |(4 : ℝ)| < |(5 : ℝ)|) hM (by simpa using hf) hnon (by simpa using hbound)
  rw [show |(4 : ℝ)|=4 by norm_num] at hj
  refine hj.trans ?_
  have hn : 0 < ‖χ.LFunction c‖ := norm_pos_iff.mpr hnon
  have hratio : M/‖χ.LFunction c‖ ≤ 2*M := by
    apply (div_le_iff₀ hn).mpr
    nlinarith [show 0 ≤ M by linarith]
  have hlog : Real.log (M/‖χ.LFunction c‖) ≤ Real.log (2*A)+Real.pi*(|T|+5)/2 := by
    have hp : 0 < M/‖χ.LFunction c‖ := div_pos (by linarith) hn
    have hh := Real.log_le_log hp hratio
    have he : 2*M=(2*A)*Real.exp (Real.pi*(|T|+5)/2) := by dsimp [M]; ring
    rw [he,Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp] at hh
    exact hh
  have hnum : Real.log (M/‖χ.LFunction c‖) ≤ (Real.log (2*A)+3*Real.pi)*(1+|T|) := by
    nlinarith [Real.pi_pos,mul_nonneg hlogA (by linarith : 0 ≤ |T|)]
  have hh := div_le_div_of_nonneg_right hnum hden.le
  convert hh using 1
  dsimp [K]
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Metric Set Filter MeromorphicOn
open scoped Topology

namespace Helfgott

theorem LFunction_shifted_disk_inputs (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ A J : ℝ,1 ≤ A ∧ 0 ≤ J ∧ ∀ V : ℝ,8 ≤ |V| →
      let f : ℂ → ℂ := fun z => χ.LFunction ((2 : ℂ)+(V : ℂ)*I+z)
      AnalyticOnNhd ℂ f (closedBall 0 5) ∧ (1/2 : ℝ) ≤ ‖f 0‖ ∧
      (∀ z ∈ closedBall 0 5,‖f z‖ ≤ A*Real.exp (Real.pi*(|V|+5)/2)) ∧
      ((∑ᶠ z : ℂ,divisor f (closedBall 0 4) z : ℤ) : ℝ) ≤ J*(1+|V|) := by
  obtain ⟨C,hC,hgrowth⟩ := LFunction_uniform_strip_exponential_bound q χ (-3) 7
  let A : ℝ := max C 1
  have hA : 1 ≤ A := le_max_right _ _
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hlogA : 0 ≤ Real.log (2*A) := Real.log_nonneg (by linarith)
  have hden : 0 < Real.log ((5 : ℝ)/4) := Real.log_pos (by norm_num)
  let J : ℝ := (Real.log (2*A)+3*Real.pi)/Real.log ((5 : ℝ)/4)
  have hJ : 0 ≤ J := div_nonneg (add_nonneg hlogA (by positivity)) hden.le
  refine ⟨A,J,hA,hJ,?_⟩
  intro V hV
  let c : ℂ := (2 : ℂ)+(V : ℂ)*I
  let f : ℂ → ℂ := fun z => χ.LFunction (c+z)
  let M : ℝ := A*Real.exp (Real.pi*(|V|+5)/2)
  have hshift (z : ℂ) (hz : z ∈ closedBall 0 5) : c+z ∈ closedBall c 5 := by
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
  have hf : AnalyticOnNhd ℂ f (closedBall 0 5) := by
    intro z hz
    have hi := (vertical_disk_im_abs_bounds V 5 (c+z) (hshift z hz)).1
    have ha : AnalyticAt ℂ χ.LFunction (c+z) := by
      apply LFunction_analyticOnNhd_off_one q χ
      intro he
      rw [he] at hi
      norm_num at hi
      linarith
    exact ha.comp (analyticAt_const.add analyticAt_id)
  have hanchor : (1/2 : ℝ) ≤ ‖f 0‖ := by
    simpa [f,c] using LFunction_right_anchor_lower_bound q χ c (by simp [c])
  have hn : f 0 ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖f 0‖ ≠ 0)
  have hb (z : ℂ) (hz : z ∈ closedBall 0 5) : ‖f z‖ ≤ M := by
    have hc := vertical_disk_coordinates V 5 (c+z) (hshift z hz)
    have hi := vertical_disk_im_abs_bounds V 5 (c+z) (hshift z hz)
    have hh := hgrowth (c+z) (by norm_num at hc ⊢; linarith [hc.1])
      (by norm_num at hc ⊢; linarith [hc.2.1]) (by linarith [hi.1])
    refine hh.trans ?_
    dsimp [M]
    gcongr
    · exact le_max_left _ _
    · exact hi.2
  have hM : 1 ≤ M := by
    have hex : 1 ≤ Real.exp (Real.pi*(|V|+5)/2) := Real.one_le_exp (by positivity)
    dsimp [M]
    nlinarith
  refine ⟨hf,hanchor,hb,?_⟩
  have hj := AnalyticOnNhd.sum_divisor_le (by norm_num : 0 < |(4 : ℝ)|)
    (by norm_num : |(4 : ℝ)| < |(5 : ℝ)|) hM (by simpa using hf) hn
    (fun z hz => hb z (by simpa using sphere_subset_closedBall hz))
  rw [show |(4 : ℝ)|=4 by norm_num] at hj
  refine hj.trans ?_
  have hnp : 0 < ‖f 0‖ := norm_pos_iff.mpr hn
  have hratio : M/‖f 0‖ ≤ 2*M := by
    apply (div_le_iff₀ hnp).mpr
    nlinarith [show 0 ≤ M by linarith]
  have hlog : Real.log (M/‖f 0‖) ≤ Real.log (2*A)+Real.pi*(|V|+5)/2 := by
    have hh := Real.log_le_log (div_pos (by linarith : 0 < M) hnp) hratio
    have he : 2*M=(2*A)*Real.exp (Real.pi*(|V|+5)/2) := by dsimp [M]; ring
    rw [he,Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp] at hh
    exact hh
  have hnum : Real.log (M/‖f 0‖) ≤ (Real.log (2*A)+3*Real.pi)*(1+|V|) := by
    nlinarith [Real.pi_pos,mul_nonneg hlogA (abs_nonneg V)]
  have hh := div_le_div_of_nonneg_right hnum hden.le
  convert hh using 1
  dsimp [J]
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Metric Set Filter MeromorphicOn Function
open scoped Topology

namespace Helfgott

lemma canonical_decomp_analytic (f g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (D : CanonicalDecomp f g R) :
    AnalyticOnNhd ℂ g (closedBall 0 R) := by
  apply D.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd.mp
  intro z
  change 0 ≤ divisor g (closedBall 0 R) z
  rw [D.divisor_eq_divisor hR]
  exact (hf.mono sphere_subset_closedBall).divisor_nonneg z

lemma canonical_decomp_finite_product (f g : ℂ → ℂ) (R : ℝ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (D : CanonicalDecomp f g R) :
    let d := divisor f (ball 0 R)
    let Z := (hf.meromorphicOn.divisor_ball_support_finite).toFinset
    f =ᶠ[codiscreteWithin (closedBall 0 R)]
      (fun z : ℂ => (∏ w ∈ Z,canonicalFactor R w z^(-d w))*g z) := by
  classical
  dsimp only
  let d := divisor f (ball 0 R)
  have hfin : d.support.Finite := hf.meromorphicOn.divisor_ball_support_finite
  have hsub : mulSupport (fun w : ℂ => (canonicalFactor R w)^(-d w)) ⊆ d.support := by
    intro w hw
    by_contra hd
    have h0 : d w=0 := notMem_support.mp hd
    have hh : (canonicalFactor R w)^(-d w) ≠ 1 := hw
    exact hh (by rw [h0]; simp)
  have he := finprod_eq_prod_of_mulSupport_subset_of_finite (fun w : ℂ => (canonicalFactor R w)^(-d w)) hsub hfin
  have hh := D.eventuallyEq
  rw [he] at hh
  filter_upwards [hh] with z hz
  simpa [d,Pi.smul_apply'] using hz

lemma canonical_decomp_eq_at (f g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (D : CanonicalDecomp f g R)
    (z : ℂ) (hz : z ∈ closedBall 0 R)
    (hn : ∀ w ∈ (hf.meromorphicOn.divisor_ball_support_finite).toFinset,z ≠ w) :
    f z=(∏ w ∈ (hf.meromorphicOn.divisor_ball_support_finite).toFinset,
      canonicalFactor R w z^(-divisor f (ball 0 R) w))*g z := by
  classical
  let Z := (hf.meromorphicOn.divisor_ball_support_finite).toFinset
  let B : ℂ → ℂ := fun z => ∏ w ∈ Z,canonicalFactor R w z^(-divisor f (ball 0 R) w)
  have hg := canonical_decomp_analytic f g R hR hf D
  have hB : AnalyticAt ℂ B z := by
    apply Finset.analyticAt_fun_prod
    intro w hw
    have hwball : w ∈ ball 0 R := (divisor f (ball 0 R)).supportWithinDomain (by simpa only [Z,Finite.mem_toFinset] using hw)
    exact (analyticOnNhd_canonicalFactor R w z (hn w hw)).zpow
      (canonicalFactor_ne_zero hwball hz (hn w hw))
  have hpre : Preperfect (closedBall (0 : ℂ) R) := by
    rw [← closure_ball (0 : ℂ) hR.ne']
    exact isOpen_ball.perfect_closure.2
  have he := (hf z hz).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hB.mul (hg z hz)).meromorphicAt hz hpre (canonical_decomp_finite_product f g R hf D)
  exact (((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hB.mul (hg z hz)).continuousAt).mp he).eq_of_nhds

lemma canonical_decomp_boundary_norm (f g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (D : CanonicalDecomp f g R)
    (z : ℂ) (hz : z ∈ sphere 0 R) : ‖g z‖=‖f z‖ := by
  classical
  have hwm (w : ℂ) (hw : w ∈ (hf.meromorphicOn.divisor_ball_support_finite).toFinset) : w ∈ ball 0 R :=
    (divisor f (ball 0 R)).supportWithinDomain (by simpa only [Finite.mem_toFinset] using hw)
  have hn (w : ℂ) (hw : w ∈ (hf.meromorphicOn.divisor_ball_support_finite).toFinset) : z ≠ w := by
    intro he
    have hh := hwm w hw
    rw [← he] at hh
    have hs := mem_sphere_zero_iff_norm.mp hz
    have hb := mem_ball_zero_iff.mp hh
    linarith
  have he := canonical_decomp_eq_at f g R hR hf D z (sphere_subset_closedBall hz) hn
  have hp : ‖∏ w ∈ (hf.meromorphicOn.divisor_ball_support_finite).toFinset,
      canonicalFactor R w z^(-divisor f (ball 0 R) w)‖=1 := by
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro w hw
    rw [norm_zpow,norm_canonicalFactor_eval_circle_eq_one (hwm w hw) hz,one_zpow]
  rw [he,norm_mul,hp,one_mul]

lemma canonical_decomp_uniform_norm (f g : ℂ → ℂ) (R M : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (D : CanonicalDecomp f g R)
    (hb : ∀ z ∈ sphere 0 R,‖f z‖ ≤ M) : ∀ z ∈ closedBall 0 R,‖g z‖ ≤ M := by
  have hg := canonical_decomp_analytic f g R hR hf D
  have hdc : DiffContOnCl ℂ g (ball 0 R) := by
    constructor
    · exact hg.differentiableOn.mono ball_subset_closedBall
    · rw [closure_ball (0 : ℂ) hR.ne']
      exact hg.continuousOn
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hdc
  · intro w hw
    have hs : w ∈ sphere 0 R := by simpa only [frontier_ball (0 : ℂ) hR.ne'] using hw
    rw [canonical_decomp_boundary_norm f g R hR hf D w hs]
    exact hb w hs
  · simpa only [closure_ball (0 : ℂ) hR.ne'] using hz

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Metric Set Filter
open scoped Topology

namespace Helfgott

theorem nonzero_analytic_disk_log (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hn : ∀ z ∈ ball 0 R,f z ≠ 0) :
    ∃ g : ℂ → ℂ,g 0=0 ∧ (∀ z ∈ ball 0 R,HasDerivAt g (deriv f z/f z) z) ∧
      ∀ z ∈ ball 0 R,Complex.exp (g z)=f z/f 0 := by
  have hfd : DifferentiableOn ℂ f (ball 0 R) := hf.differentiableOn
  have hld : DifferentiableOn ℂ (fun z => deriv f z/f z) (ball 0 R) :=
    (hfd.deriv isOpen_ball).div hfd hn
  obtain ⟨g,hg0,hg⟩ := hld.isExactOn_ball.with_val_at 0 0
  have hh (z : ℂ) (hz : z ∈ ball 0 R) :
      HasDerivAt (fun w => f w*Complex.exp (-g w)) 0 z := by
    have ht := ((hf z hz).differentiableAt.hasDerivAt).mul ((hg z hz).neg.cexp)
    simp only [Pi.neg_apply] at ht
    have hzero : deriv f z*Complex.exp (-g z)+f z*(Complex.exp (-g z)* -(deriv f z/f z))=0 := by
      field_simp [hn z hz]
      ring
    rw [hzero] at ht
    simpa only [Pi.mul_apply] using! ht
  have hhd : DifferentiableOn ℂ (fun w => f w*Complex.exp (-g w)) (ball 0 R) :=
    fun z hz => (hh z hz).differentiableAt.differentiableWithinAt
  have h0 : f 0 ≠ 0 := hn 0 (mem_ball_self hR)
  refine ⟨g,hg0,hg,?_⟩
  intro z hz
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected hhd
    (fun w hw => (hh w hw).deriv) hz (mem_ball_self hR)
  simp only [hg0,neg_zero,Complex.exp_zero,mul_one,Complex.exp_neg] at he
  field_simp [h0,Complex.exp_ne_zero] at he ⊢
  linear_combination -he

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Metric Set Filter
open scoped Topology

namespace Helfgott

theorem nonzero_disk_logDeriv_bound (f : ℂ → ℂ) (M : ℝ)
    (hf : AnalyticOnNhd ℂ f (ball 0 4)) (hn : ∀ z ∈ ball 0 4,f z ≠ 0)
    (hb : ∀ z ∈ ball 0 4,‖f z‖ ≤ M) :
    ∀ z : ℂ,‖z‖ ≤ 3 → ‖deriv f z/f z‖ ≤ 56*(1+Real.log (M/‖f 0‖)) := by
  have h0 : f 0 ≠ 0 := hn 0 (mem_ball_self (by norm_num))
  have h0p : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hM0 : ‖f 0‖ ≤ M := hb 0 (mem_ball_self (by norm_num))
  have hM : 0 < M := h0p.trans_le hM0
  obtain ⟨g,hg0,hg,he⟩ := nonzero_analytic_disk_log f 4 (by norm_num) hf hn
  let H : ℝ := 1+Real.log (M/‖f 0‖)
  have hlog : 0 ≤ Real.log (M/‖f 0‖) :=
    Real.log_nonneg ((one_le_div h0p).mpr hM0)
  have hH : 0 < H := by dsimp [H]; linarith
  have hgd : DifferentiableOn ℂ g (ball 0 4) :=
    fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  have hre : MapsTo g (ball 0 4) {w : ℂ | w.re ≤ H} := by
    intro z hz
    have hex := congrArg norm (he z hz)
    simp only [norm_exp,norm_div] at hex
    have hh := congrArg Real.log hex
    rw [Real.log_exp] at hh
    have hzpos : 0 < ‖f z‖/‖f 0‖ := div_pos (norm_pos_iff.mpr (hn z hz)) h0p
    have hratio : ‖f z‖/‖f 0‖ ≤ M/‖f 0‖ := div_le_div_of_nonneg_right (hb z hz) h0p.le
    change (g z).re ≤ H
    rw [hh]
    exact (Real.log_le_log hzpos hratio).trans (by dsimp [H]; linarith)
  have hgb (w : ℂ) (hw : ‖w‖ < 7/2) : ‖g w‖ ≤ 14*H := by
    have hw4 : w ∈ ball 0 4 := mem_ball_zero_iff.mpr (by linarith)
    have hh := Complex.borelCaratheodory_zero hH hgd hre (by norm_num : (0 : ℝ)<4) hw4 hg0
    refine hh.trans ?_
    apply (div_le_iff₀ (by linarith : 0 < 4-‖w‖)).mpr
    nlinarith
  intro z hz
  have hz4 : z ∈ ball 0 4 := mem_ball_zero_iff.mpr (by linarith)
  have hsub : ball z (1/2 : ℝ) ⊆ ball (0 : ℂ) 4 := by
    intro w hw
    have hnorm : ‖w‖ ≤ ‖w-z‖+‖z‖ := norm_le_norm_sub_add w z
    have hw' : ‖w-z‖ < 1/2 := by simpa only [mem_ball,dist_eq_norm] using hw
    exact mem_ball_zero_iff.mpr (by linarith)
  have hmaps : MapsTo g (ball z (1/2 : ℝ)) (closedBall (g z) (28*H)) := by
    intro w hw
    have hnorm : ‖w‖ ≤ ‖w-z‖+‖z‖ := norm_le_norm_sub_add w z
    have hw' : ‖w-z‖ < 1/2 := by simpa only [mem_ball,dist_eq_norm] using hw
    have hgw := hgb w (by linarith)
    have hgz := hgb z (by linarith)
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith)
  have hd := Complex.norm_deriv_le_div_of_mapsTo_ball (hgd.mono hsub) hmaps (by norm_num : (0 : ℝ)<1/2)
  rw [(hg z hz4).deriv] at hd
  convert hd using 1
  dsimp [H]
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Metric Set Filter MeromorphicOn Function
open scoped Topology ComplexConjugate

namespace Helfgott

lemma norm_canonical_at_zero_ge_one (R : ℝ) (w : ℂ) (hR : 0 < R)
    (hw : w ∈ ball 0 R) (hw0 : w ≠ 0) : 1 ≤ ‖canonicalFactor R w 0‖ := by
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwb : ‖w‖ < R := mem_ball_zero_iff.mp hw
  simp only [canonicalFactor_apply,mul_zero,sub_zero,zero_sub,norm_div,norm_pow,norm_real,
    Real.norm_eq_abs,abs_of_pos hR,norm_mul,norm_neg]
  apply (le_div_iff₀ (mul_pos hR hwp)).mpr
  nlinarith

lemma canonical_decomp_anchor_lower (f g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (D : CanonicalDecomp f g R)
    (h0 : f 0 ≠ 0) : ‖f 0‖ ≤ ‖g 0‖ := by
  classical
  let Z := (hf.meromorphicOn.divisor_ball_support_finite).toFinset
  have hz0 : 0 ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  have hd0 : divisor f (ball 0 R) 0=0 := by
    rw [divisor_apply (hf.meromorphicOn.mono_set ball_subset_closedBall) (mem_ball_self hR),
      (hf 0 hz0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]
    simp
  have hwm (w : ℂ) (hw : w ∈ Z) : w ∈ ball 0 R :=
    (divisor f (ball 0 R)).supportWithinDomain (by simpa only [Z,Finite.mem_toFinset] using hw)
  have hw0 (w : ℂ) (hw : w ∈ Z) : w ≠ 0 := by
    intro he
    subst w
    have hh : divisor f (ball 0 R) 0 ≠ 0 := by simpa only [Z,Finite.mem_toFinset,mem_support] using hw
    exact hh hd0
  have he := canonical_decomp_eq_at f g R hR hf D 0 hz0 (fun w hw => (hw0 w hw).symm)
  have hp : ‖∏ w ∈ Z,canonicalFactor R w 0^(-divisor f (ball 0 R) w)‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro w hw; exact norm_nonneg _
    · intro w hw
      rw [norm_zpow]
      apply zpow_le_one_of_nonpos₀ (norm_canonical_at_zero_ge_one R w hR (hwm w hw) (hw0 w hw))
      exact neg_nonpos.mpr ((hf.mono ball_subset_closedBall).divisor_nonneg w)
  rw [he,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hp

lemma canonicalFactor_logDeriv_formula (w z : ℂ) (hzw : z ≠ w)
    (hnum : (16 : ℂ)-conj w*z ≠ 0) :
    logDeriv (canonicalFactor 4 w) z= -(conj w)/((16 : ℂ)-conj w*z)-1/(z-w) := by
  let P : ℂ → ℂ := fun t => (16 : ℂ)-conj w*t
  let Q : ℂ → ℂ := fun t => (4 : ℂ)*(t-w)
  have hp : HasDerivAt P (-conj w) z := by
    simpa only [P,id_eq,mul_one] using! (hasDerivAt_id z).const_mul (conj w) |>.const_sub (16 : ℂ)
  have hq : HasDerivAt Q 4 z := by
    simpa only [Q,id_eq,mul_one] using! ((hasDerivAt_id z).sub_const w).const_mul (4 : ℂ)
  have hqn : Q z ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr hzw)
  have hh := logDeriv_div (f:=P) (g:=Q) z hnum hqn hp.differentiableAt hq.differentiableAt
  change logDeriv (fun t => (4^2-conj w*t)/(4*(t-w))) z=_
  have he : (fun t : ℂ => (4^2-conj w*t)/(4*(t-w)))=(fun t => P t/Q t) := by dsimp [P,Q]; norm_num
  rw [he,hh,logDeriv_apply,logDeriv_apply,hp.deriv,hq.deriv]
  dsimp [P,Q]
  field_simp <;> ring

lemma canonicalFactor_logDeriv_bound (w z : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hw : ‖w‖ < 4) (hz : ‖z‖ ≤ 3) (hd : δ ≤ ‖z-w‖) :
    ‖logDeriv (canonicalFactor 4 w) z‖ ≤ 1+1/δ := by
  have hzw : z ≠ w := by intro he; rw [he,sub_self,norm_zero] at hd; linarith
  have hprod : ‖conj w*z‖ ≤ 12 := by
    rw [norm_mul,norm_conj]
    nlinarith [norm_nonneg w,norm_nonneg z]
  have hden : 4 ≤ ‖(16 : ℂ)-conj w*z‖ := by
    have hh := norm_le_norm_sub_add (16 : ℂ) (conj w*z)
    norm_num at hh
    simp only [norm_mul,norm_conj] at hprod
    linarith
  have hn : (16 : ℂ)-conj w*z ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖(16 : ℂ)-conj w*z‖ ≠ 0)
  rw [canonicalFactor_logDeriv_formula w z hzw hn]
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_div,norm_neg,norm_conj,norm_one]
  have h1 : ‖w‖/‖(16 : ℂ)-conj w*z‖ ≤ 1 := (div_le_one₀ (by linarith)).mpr (by linarith)
  have h2 : 1/‖z-w‖ ≤ 1/δ := one_div_le_one_div_of_le hδ hd
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Metric Set Filter MeromorphicOn Function
open scoped Topology

namespace Helfgott

theorem analytic_disk_logDeriv_away_zeros (f : ℂ → ℂ) (M δ : ℝ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 4)) (h0 : f 0 ≠ 0)
    (hb : ∀ w ∈ closedBall 0 4,‖f w‖ ≤ M) (hδ : 0 < δ)
    (z : ℂ) (hz : ‖z‖ ≤ 3)
    (hd : ∀ w ∈ ball 0 4,f w=0 → δ ≤ ‖z-w‖) :
    f z ≠ 0 ∧ ‖deriv f z/f z‖ ≤
      56*(1+Real.log (M/‖f 0‖))+
      ((∑ᶠ w : ℂ,divisor f (ball 0 4) w : ℤ) : ℝ)*(1+1/δ) := by
  classical
  have hzball : z ∈ ball (0 : ℂ) 4 := mem_ball_zero_iff.mpr (by linarith)
  have hz0 : 0 ∈ closedBall (0 : ℂ) 4 := mem_closedBall_self (by norm_num)
  have htop : ∀ u : closedBall (0 : ℂ) 4,meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    have ho : meromorphicOrderAt f 0=0 := (hf 0 hz0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0
    apply hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (convex_closedBall (0 : ℂ) 4).isPreconnected hz0 u.property
    rw [ho]
    simp
  obtain ⟨g,D⟩ := hf.meromorphicOn.exists_canonicalDecomp htop
  have hg := canonical_decomp_analytic f g 4 (by norm_num) hf D
  have hgb := canonical_decomp_uniform_norm f g 4 M (by norm_num) hf D (fun w hw => hb w (sphere_subset_closedBall hw))
  have hanchor := canonical_decomp_anchor_lower f g 4 (by norm_num) hf D h0
  have hgn0 : g 0 ≠ 0 := D.ne_zero 0 (mem_ball_self (by norm_num))
  have hgnz : g z ≠ 0 := D.ne_zero z hzball
  have h0p : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hg0p : 0 < ‖g 0‖ := norm_pos_iff.mpr hgn0
  have hMp : 0 < M := h0p.trans_le (hb 0 hz0)
  have hlg := nonzero_disk_logDeriv_bound g M (hg.mono ball_subset_closedBall) D.ne_zero
    (fun w hw => hgb w (ball_subset_closedBall hw)) z hz
  have hgratio : M/‖g 0‖ ≤ M/‖f 0‖ := div_le_div_of_nonneg_left hMp.le h0p hanchor
  have hlog := Real.log_le_log (div_pos hMp hg0p) hgratio
  have hlg' : ‖logDeriv g z‖ ≤ 56*(1+Real.log (M/‖f 0‖)) := by
    rw [logDeriv_apply]
    exact hlg.trans (by linarith)
  let d := divisor f (ball 0 4)
  have hfin : d.support.Finite := hf.meromorphicOn.divisor_ball_support_finite
  let Z := hfin.toFinset
  have hwm (w : ℂ) (hw : w ∈ Z) : w ∈ ball 0 4 := d.supportWithinDomain (by simpa only [Z,Finite.mem_toFinset] using hw)
  have hwzero (w : ℂ) (hw : w ∈ Z) : f w=0 := by
    by_contra hn
    have hdw : d w ≠ 0 := by simpa only [Z,Finite.mem_toFinset,mem_support] using hw
    apply hdw
    dsimp [d]
    rw [divisor_apply (hf.meromorphicOn.mono_set ball_subset_closedBall) (hwm w hw),
      (hf w (ball_subset_closedBall (hwm w hw))).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn]
    simp
  have hdist (w : ℂ) (hw : w ∈ Z) : δ ≤ ‖z-w‖ := hd w (hwm w hw) (hwzero w hw)
  have hn (w : ℂ) (hw : w ∈ Z) : z ≠ w := by
    intro he
    have hh := hdist w hw
    rw [he,sub_self,norm_zero] at hh
    linarith
  let B : ℂ → ℂ := fun t => ∏ w ∈ Z,canonicalFactor 4 w t^(-d w)
  have hfact (w : ℂ) (hw : w ∈ Z) : canonicalFactor 4 w z ≠ 0 :=
    canonicalFactor_ne_zero (hwm w hw) (ball_subset_closedBall hzball) (hn w hw)
  have hfd (w : ℂ) (hw : w ∈ Z) : DifferentiableAt ℂ (canonicalFactor 4 w) z :=
    (analyticOnNhd_canonicalFactor 4 w z (hn w hw)).differentiableAt
  have hBn : B z ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w hw => zpow_ne_zero _ (hfact w hw))
  have hBd : DifferentiableAt ℂ B z := DifferentiableAt.fun_finsetProd (fun w hw => (hfd w hw).zpow (.inl (hfact w hw)))
  have heN : f =ᶠ[𝓝 z] (fun t => B t*g t) := by
    have hnN : ∀ᶠ t in 𝓝 z,∀ w ∈ Z,t ≠ w :=
      (eventually_all_finset Z).mpr (fun w hw => isOpen_ne.mem_nhds (hn w hw))
    filter_upwards [isOpen_ball.mem_nhds hzball,hnN] with t ht htn
    exact canonical_decomp_eq_at f g 4 (by norm_num) hf D t (ball_subset_closedBall ht) htn
  have hid : logDeriv f z=logDeriv B z+logDeriv g z := by
    rw [(logDeriv_congr_nhds heN).eq_of_nhds]
    exact logDeriv_mul z hBn hgnz hBd (hg z (ball_subset_closedBall hzball)).differentiableAt
  have hsum : logDeriv B z=∑ w ∈ Z,((-d w : ℤ) : ℂ)*logDeriv (canonicalFactor 4 w) z := by
    change logDeriv (fun t : ℂ => ∏ w ∈ Z,canonicalFactor 4 w t^(-d w)) z=_
    have hp := logDeriv_prod (f:=fun w : ℂ => fun t : ℂ => canonicalFactor 4 w t^(-d w)) (x:=z)
      (fun w hw => zpow_ne_zero _ (hfact w hw))
      (fun w hw => (hfd w hw).zpow (.inl (hfact w hw)))
    rw [hp]
    apply Finset.sum_congr rfl
    intro w hw
    exact logDeriv_fun_zpow (hfd w hw) (-d w)
  have hbnorm : ‖logDeriv B z‖ ≤ (∑ w ∈ Z,(d w : ℝ))*(1+1/δ) := by
    rw [hsum,Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro w hw
    have hdnon : 0 ≤ d w := (hf.mono ball_subset_closedBall).divisor_nonneg w
    have hdreal : 0 ≤ (d w : ℝ) := by exact_mod_cast hdnon
    rw [norm_mul,Complex.norm_intCast,Int.cast_neg,abs_neg,abs_of_nonneg hdreal]
    apply mul_le_mul_of_nonneg_left _ hdreal
    exact canonicalFactor_logDeriv_bound w z δ hδ (mem_ball_zero_iff.mp (hwm w hw)) hz (hdist w hw)
  have hN : (∑ w ∈ Z,(d w : ℝ))=((∑ᶠ w : ℂ,d w : ℤ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset_of_finite (fun w : ℂ => d w) subset_rfl hfin]
    simp only [Int.cast_sum,Z]
  rw [hN] at hbnorm
  refine ⟨?_,?_⟩
  · have he := heN.eq_of_nhds
    rw [he]
    exact mul_ne_zero hBn hgnz
  · rw [← logDeriv_apply,hid]
    exact (norm_add_le _ _).trans (by dsimp [d] at hbnorm; linarith)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Metric Set Filter MeromorphicOn Function
open scoped Topology

namespace Helfgott

lemma analytic_disk_zero_mem_divisor_support (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 4)) (h0 : f 0 ≠ 0)
    (w : ℂ) (hw : w ∈ closedBall 0 4) (hz : f w=0) :
    w ∈ (divisor f (closedBall 0 4)).support := by
  have hz0 : (0 : ℂ) ∈ closedBall 0 4 := mem_closedBall_self (by norm_num)
  have ho : meromorphicOrderAt f 0=0 :=
    (hf 0 hz0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0
  have htop : meromorphicOrderAt f w ≠ ⊤ := by
    apply hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) 4).isPreconnected hz0 hw
    rw [ho]
    simp
  rw [mem_support,divisor_apply hf.meromorphicOn hw]
  intro he
  have hoz : meromorphicOrderAt f w=0 := by
    rw [← WithTop.coe_untop₀_of_ne_top htop,he]
    rfl
  exact ((hf w hw).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hoz) hz

lemma analytic_disk_divisor_card_le (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 4)) :
    let hfin := (divisor f (closedBall 0 4)).finiteSupport (isCompact_closedBall 0 4)
    (hfin.toFinset.card : ℝ) ≤ ((∑ᶠ w : ℂ,divisor f (closedBall 0 4) w : ℤ) : ℝ) := by
  classical
  let d := divisor f (closedBall 0 4)
  let hfin := d.finiteSupport (isCompact_closedBall 0 4)
  let Z := hfin.toFinset
  change (Z.card : ℝ) ≤ ((∑ᶠ w : ℂ,d w : ℤ) : ℝ)
  rw [finsum_eq_sum_of_support_subset_of_finite (fun w : ℂ => d w) subset_rfl hfin,Int.cast_sum]
  have hone (w : ℂ) (hw : w ∈ Z) : (1 : ℝ) ≤ (d w : ℝ) := by
    have hn : d w ≠ 0 := by simpa only [Z,Finite.mem_toFinset,mem_support] using hw
    have hp : 0 ≤ d w := hf.divisor_nonneg w
    have hi : (1 : ℤ) ≤ d w := by omega
    exact_mod_cast hi
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one]
    using Finset.sum_le_sum (s:=Z) hone

lemma analytic_disk_divisor_sum_ball_le_closed (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 4)) :
    ((∑ᶠ w : ℂ,divisor f (ball 0 4) w : ℤ) : ℝ) ≤
      ((∑ᶠ w : ℂ,divisor f (closedBall 0 4) w : ℤ) : ℝ) := by
  classical
  let d := divisor f (closedBall 0 4)
  let hfin := d.finiteSupport (isCompact_closedBall 0 4)
  have hsub : (divisor f (ball 0 4)).support ⊆ d.support := by
    intro w hw
    have hm := (divisor f (ball 0 4)).supportWithinDomain hw
    simpa only [mem_support,divisor_apply (hf.meromorphicOn.mono_set ball_subset_closedBall) hm,
      d,divisor_apply hf.meromorphicOn (ball_subset_closedBall hm)] using hw
  rw [finsum_eq_sum_of_support_subset_of_finite _ hsub hfin,
    finsum_eq_sum_of_support_subset_of_finite (fun w : ℂ => d w) subset_rfl hfin,
    Int.cast_sum,Int.cast_sum]
  apply Finset.sum_le_sum
  intro w hw
  by_cases hm : w ∈ ball (0 : ℂ) 4
  · rw [divisor_apply (hf.meromorphicOn.mono_set ball_subset_closedBall) hm]
    dsimp [d]
    rw [divisor_apply hf.meromorphicOn (ball_subset_closedBall hm)]
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hm]
    exact_mod_cast hf.divisor_nonneg w

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Metric

namespace Helfgott

theorem finite_height_separation (S : Finset ℝ) (T : ℝ) :
    ∃ t : ℝ,T<t ∧ t<T+1 ∧ ∀ v ∈ S,1/(4*((S.card : ℝ)+1)) ≤ |t-v| := by
  classical
  let δ : ℝ := 1/(4*((S.card : ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hb : volume (⋃ v ∈ S,ball v δ) < 1 := by
    refine (measure_biUnion_finset_le S (fun v => ball v δ)).trans_lt ?_
    simp_rw [Real.volume_ball]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun v hv => (by positivity : 0 ≤ 2*δ))]
    simp only [Finset.sum_const,nsmul_eq_mul]
    apply ENNReal.ofReal_lt_one.mpr
    dsimp [δ]
    have hn : 0 ≤ (S.card : ℝ) := by positivity
    field_simp
    nlinarith
  have hint : volume (Ioo T (T+1))=1 := by rw [Real.volume_Ioo]; norm_num
  have hsub : ¬Ioo T (T+1) ⊆ ⋃ v ∈ S,ball v δ := by
    intro h
    have hh := measure_mono (μ:=volume) h
    rw [hint] at hh
    exact not_le_of_gt hb hh
  obtain ⟨t,ht,hbad⟩ := Set.not_subset.mp hsub
  refine ⟨t,ht.1,ht.2,?_⟩
  intro v hv
  by_contra hd
  have hlt : |t-v| < δ := lt_of_not_ge hd
  apply hbad
  exact mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨hv,by simpa only [mem_ball,Real.dist_eq] using hlt⟩⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000
open Complex Metric Set Filter MeromorphicOn Function
open scoped Topology

namespace Helfgott

theorem LFunction_selected_horizontal_log_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ T : ℝ,8 ≤ T →
      ∃ u : ℝ,T<u ∧ u<T+1 ∧ ∀ σ v : ℝ,
        -(1/2 : ℝ) ≤ σ → σ ≤ 2 → (v=u ∨ v=-u) →
        χ.LFunction ((σ : ℂ)+(v : ℂ)*I) ≠ 0 ∧
        ‖deriv χ.LFunction ((σ : ℂ)+(v : ℂ)*I)/
          χ.LFunction ((σ : ℂ)+(v : ℂ)*I)‖ ≤ C*(1+T)^2 := by
  classical
  obtain ⟨A,J,hA,hJ,hinputs⟩ := LFunction_shifted_disk_inputs q χ
  let B : ℝ := 56*(1+Real.log (2*A)+3*Real.pi)
  let C : ℝ := B+2*J*(16*J+5)
  have hlogA : 0 ≤ Real.log (2*A) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T hT
  let V : ℝ := T+1/2
  let H : ℝ := 1+T
  have hVp : 0 < V := by dsimp [V]; linarith
  have hH : 1 ≤ H := by dsimp [H]; linarith
  let c (b : Bool) : ℂ := (2 : ℂ)+((if b then V else -V : ℝ) : ℂ)*I
  let f (b : Bool) : ℂ → ℂ := fun z => χ.LFunction (c b+z)
  have hVb (b : Bool) : |(if b then V else -V : ℝ)|=V := by
    cases b <;> simp [abs_of_pos hVp]
  have hi (b : Bool) : AnalyticOnNhd ℂ (f b) (closedBall 0 5) ∧
      (1/2 : ℝ) ≤ ‖f b 0‖ ∧
      (∀ z ∈ closedBall 0 5,‖f b z‖ ≤ A*Real.exp (Real.pi*(V+5)/2)) ∧
      ((∑ᶠ z : ℂ,divisor (f b) (closedBall 0 4) z : ℤ) : ℝ) ≤ J*(1+V) := by
    have hh := hinputs (if b then V else -V) (by rw [hVb]; dsimp [V]; linarith)
    simpa only [hVb,c,f] using hh
  have hf (b : Bool) : AnalyticOnNhd ℂ (f b) (closedBall 0 4) :=
    (hi b).1.mono (closedBall_subset_closedBall (by norm_num))
  have hanchor (b : Bool) : f b 0 ≠ 0 :=
    norm_ne_zero_iff.mp (by linarith [(hi b).2.1] : ‖f b 0‖ ≠ 0)
  let d (b : Bool) := divisor (f b) (closedBall 0 4)
  let hfin (b : Bool) := (d b).finiteSupport (isCompact_closedBall 0 4)
  let Z (b : Bool) := (hfin b).toFinset
  have hN (b : Bool) : ((∑ᶠ z : ℂ,d b z : ℤ) : ℝ) ≤ 2*J*H := by
    refine (hi b).2.2.2.trans ?_
    dsimp [V,H]
    nlinarith
  have hcard (b : Bool) : ((Z b).card : ℝ) ≤ 2*J*H :=
    (analytic_disk_divisor_card_le (f b) (hf b)).trans (hN b)
  let S : Finset ℝ := (Z true).image (fun w => |(c true+w).im|) ∪
    (Z false).image (fun w => |(c false+w).im|)
  have hScard : (S.card : ℝ) ≤ 4*J*H := by
    have hh : S.card ≤ (Z true).card+(Z false).card :=
      (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
    have hr : (S.card : ℝ) ≤ ((Z true).card : ℝ)+((Z false).card : ℝ) := by exact_mod_cast hh
    linarith [hcard true,hcard false]
  obtain ⟨u,hu0,hu1,hsep⟩ := finite_height_separation S T
  have hup : 0 < u := by linarith
  let δ : ℝ := 1/(4*((S.card : ℝ)+1))
  have hcardnon : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hδ : 0 < δ := by
    change 0 < 1/(4*((S.card : ℝ)+1))
    exact one_div_pos.mpr (mul_pos (by norm_num) (by linarith))
  have hδinv : 1/δ=4*((S.card : ℝ)+1) := by dsimp [δ]; rw [one_div_one_div]
  have hδbound : 1+1/δ ≤ (16*J+5)*H := by rw [hδinv]; nlinarith
  let M : ℝ := A*Real.exp (Real.pi*(V+5)/2)
  have hMp : 0 < M := by dsimp [M]; positivity
  have hlog (b : Bool) : 56*(1+Real.log (M/‖f b 0‖)) ≤ B*H := by
    have hnp : 0 < ‖f b 0‖ := norm_pos_iff.mpr (hanchor b)
    have hratio : M/‖f b 0‖ ≤ 2*M := by
      apply (div_le_iff₀ hnp).mpr
      nlinarith [(hi b).2.1]
    have hl := Real.log_le_log (div_pos hMp hnp) hratio
    have he : 2*M=(2*A)*Real.exp (Real.pi*(V+5)/2) := by dsimp [M]; ring
    rw [he,Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp] at hl
    dsimp [B,V,H] at *
    nlinarith [Real.pi_pos,mul_nonneg hlogA (by linarith : 0 ≤ T)]
  have hbound (σ : ℝ) (b : Bool) (hσ0 : -(1/2 : ℝ) ≤ σ) (hσ1 : σ ≤ 2) :
      let v : ℝ := if b then u else -u
      χ.LFunction ((σ : ℂ)+(v : ℂ)*I) ≠ 0 ∧
      ‖deriv χ.LFunction ((σ : ℂ)+(v : ℂ)*I)/
        χ.LFunction ((σ : ℂ)+(v : ℂ)*I)‖ ≤ C*H^2 := by
    let v : ℝ := if b then u else -u
    let s : ℂ := (σ : ℂ)+(v : ℂ)*I
    let z : ℂ := s-c b
    have hcz : c b+z=s := by dsimp [z]; ring
    have hz : ‖z‖ ≤ 3 := by
      have hh := Complex.norm_le_abs_re_add_abs_im z
      have hr : |z.re| ≤ (5/2 : ℝ) := by
        dsimp [z,s,c]
        simp
        rw [abs_of_nonpos (by linarith : σ-2 ≤ 0)]
        linarith
      have him : |z.im| ≤ (1/2 : ℝ) := by
        cases b <;> dsimp [z,s,c,v,V] <;> simp <;> apply abs_le.mpr <;> constructor <;> linarith
      linarith
    have hsd : ∀ w ∈ ball (0 : ℂ) 4,f b w=0 → δ ≤ ‖z-w‖ := by
      intro w hw hw0
      have hwZ : w ∈ Z b := by
        simpa only [Z,Finite.mem_toFinset,d] using
          analytic_disk_zero_mem_divisor_support (f b) (hf b) (hanchor b) w
            (ball_subset_closedBall hw) hw0
      have hwS : |(c b+w).im| ∈ S := by
        cases b
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w,hwZ,rfl⟩)
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w,hwZ,rfl⟩)
      have hsabs : |s.im|=u := by cases b <;> simp [s,v,abs_of_pos hup]
      have hh := hsep _ hwS
      have hab : |u-(|(c b+w).im|)| ≤ |s.im-(c b+w).im| := by
        rw [← hsabs]
        exact abs_abs_sub_abs_le_abs_sub _ _
      have he : s-(c b+w)=z-w := by dsimp [z]; ring
      have hnorm : |s.im-(c b+w).im| ≤ ‖z-w‖ := by
        calc
          _ ≤ ‖s-(c b+w)‖ := by simpa only [sub_im] using Complex.abs_im_le_norm (s-(c b+w))
          _ = ‖z-w‖ := by rw [he]
      exact hh.trans (hab.trans hnorm)
    obtain ⟨hn,hlogbound⟩ := analytic_disk_logDeriv_away_zeros (f b) M δ (hf b)
      (hanchor b) (fun w hw => (hi b).2.2.1 w (closedBall_subset_closedBall (by norm_num) hw))
      hδ z hz hsd
    have hfz : f b z=χ.LFunction s := by simp only [f,hcz]
    have hder : deriv (f b) z=deriv χ.LFunction s := by
      have ha := (hf b z (mem_closedBall_zero_iff.mpr (by linarith)))
      have hd : DifferentiableAt ℂ χ.LFunction s := by
        apply (LFunction_analyticOnNhd_off_one q χ s ?_).differentiableAt
        intro he
        have hsabs : |s.im|=u := by cases b <;> simp [s,v,abs_of_pos hup]
        rw [he] at hsabs
        norm_num at hsabs
        linarith
      have hd' : HasDerivAt χ.LFunction (deriv χ.LFunction s) (c b+z) := by rw [hcz]; exact hd.hasDerivAt
      have hh := hd'.comp z ((hasDerivAt_const z (c b)).add (hasDerivAt_id z))
      simpa only [f,hcz,zero_add,mul_one,Function.comp_def,Pi.add_apply,id_eq] using! hh.deriv
    have hNball : ((∑ᶠ w : ℂ,divisor (f b) (ball 0 4) w : ℤ) : ℝ) ≤ 2*J*H :=
      (analytic_disk_divisor_sum_ball_le_closed (f b) (hf b)).trans (hN b)
    have hterm : ((∑ᶠ w : ℂ,divisor (f b) (ball 0 4) w : ℤ) : ℝ)*(1+1/δ) ≤
        2*J*(16*J+5)*H^2 := by
      calc
        _ ≤ (2*J*H)*((16*J+5)*H) :=
          mul_le_mul hNball hδbound (by linarith [le_of_lt (one_div_pos.mpr hδ)])
            (mul_nonneg (mul_nonneg (by norm_num) hJ) (by linarith))
        _ = _ := by ring
    have hBH : B*H ≤ B*H^2 := by nlinarith [mul_nonneg hB (by nlinarith : 0 ≤ H^2-H)]
    refine ⟨by rwa [hfz] at hn,?_⟩
    rw [hder,hfz] at hlogbound
    dsimp [C]
    nlinarith [hlog b]
  refine ⟨u,hu0,hu1,?_⟩
  intro σ v hσ0 hσ1 hv
  rcases hv with rfl|rfl
  · simpa only [Bool.true_eq_false,Bool.false_eq_true,ite_true,H] using hbound σ true hσ0 hσ1
  · simpa only [Bool.true_eq_false,Bool.false_eq_true,ite_false,H] using hbound σ false hσ0 hσ1

end Helfgott
end

open Complex Metric Set Filter MeromorphicOn Function
open scoped Topology

theorem solution (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ T : ℝ,8 ≤ T →
      ∃ u : ℝ,T<u ∧ u<T+1 ∧ ∀ σ v : ℝ,
        -(1/2 : ℝ) ≤ σ → σ ≤ 2 → (v=u ∨ v=-u) →
        χ.LFunction ((σ : ℂ)+(v : ℂ)*I) ≠ 0 ∧
        ‖deriv χ.LFunction ((σ : ℂ)+(v : ℂ)*I)/
          χ.LFunction ((σ : ℂ)+(v : ℂ)*I)‖ ≤ C*(1+T)^2 := Helfgott.LFunction_selected_horizontal_log_bound q χ

#print axioms solution
