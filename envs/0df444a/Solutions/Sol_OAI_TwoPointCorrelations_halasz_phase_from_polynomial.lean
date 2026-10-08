-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_phase_from_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:34:13.92438+00:00
-- url     : https://prove2.me/submissions/81bda66d-9d18-4dc3-b736-4fadd4772523

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovDiagonal
namespace OAI

/-! The diagonal algebra for the complete Vinogradov system: its first
s power sums determine all elementary symmetric functions of s entries.
This is the finite algebraic starting point for the mean-value argument
underlying Ford's logarithmic exponential-sum estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MvPolynomial




@[simp] lemma mem_halaszVinogradovFiber {s N k : ℕ} {x y : Fin s → Fin N} :
    y ∈ halaszVinogradovFiber x k ↔ ∀ j ∈ Icc 1 k,
      (∑ i, ((x i).val+1)^j) = ∑ i, ((y i).val+1)^j := by
  classical
  simp [halaszVinogradovFiber]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCircleWindow
namespace OAI

/-! A compact circle window with a lower bound for its small Fourier
coefficients. This supplies the localizer for the double moment estimate. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ComplexConjugate

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogTaylor
namespace OAI

/-! A uniform logarithmic Taylor remainder for the short multiplicative
shifts in the double mean-value method. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Complex


lemma halasz_log_taylor_remainder (k : ℕ) {z h : ℝ}
    (hz : 0< z) (hh : 0≤ h) (hhz : h≤ z/2) :
    |Real.log (z+h)-Real.log z-halaszLogTaylor k z h|≤2*(h/z)^(k+1) := by
  have hu : 0≤ h/z := div_nonneg hh hz.le
  have hu2 : h/z≤1/2 := (div_le_iff₀ hz).mpr (by linarith)
  have hu1 : |-(h/z)|<1 := by rw [abs_neg,abs_of_nonneg hu]; linarith
  have hl := Real.abs_log_sub_add_sum_range_le hu1 k
  have he : (∑ i∈range k, (-(h/z))^(i+1)/((i+1:ℕ):ℝ)) =
      -halaszLogTaylor k z h := by
    rw [halaszLogTaylor,← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    rw [neg_eq_neg_one_mul,mul_pow,pow_succ (-1:ℝ)]
    push_cast
    ring
  simp only [Nat.cast_add,Nat.cast_one] at he
  rw [he,sub_neg_eq_add,abs_neg,abs_of_nonneg hu] at hl
  have hlog : Real.log (z+h)=Real.log z+Real.log (1+h/z) := by
    rw [← Real.log_mul hz.ne' (by linarith : 1+h/z≠0)]
    congr 1
    field_simp
  rw [hlog]
  have hden : (h/z)^(k+1)/(1-h/z)≤2*(h/z)^(k+1) := by
    apply (div_le_iff₀ (by linarith : 0<1-h/z)).mpr
    nlinarith [pow_nonneg hu (k+1)]
  convert (preTransparency := .instances) hl.trans hden using 1
  congr 1
  ring

lemma halasz_exp_phase_lipschitz (x y : ℝ) :
    ‖Complex.exp (Complex.I*(x:ℂ))-Complex.exp (Complex.I*(y:ℂ))‖≤|x-y| := by
  have he : Complex.exp (Complex.I*(x:ℂ))-Complex.exp (Complex.I*(y:ℂ))=
      Complex.exp (Complex.I*(y:ℂ))*
        (Complex.exp (Complex.I*((x-y:ℝ):ℂ))-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_exp_I_mul_ofReal,one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y))

lemma halasz_log_taylor_phase (k : ℕ) {z h : ℝ} (t : ℝ)
    (hz : 0< z) (hh : 0≤ h) (hhz : h≤ z/2) :
    ‖Complex.exp (Complex.I*((t*Real.log (z+h):ℝ):ℂ))-
      Complex.exp (Complex.I*((t*(Real.log z+halaszLogTaylor k z h):ℝ):ℂ))‖≤
      2*|t| *(h/z)^(k+1) := by
  have hp := halasz_exp_phase_lipschitz (t*Real.log (z+h))
    (t*(Real.log z+halaszLogTaylor k z h))
  have he : t*Real.log (z+h)-t*(Real.log z+halaszLogTaylor k z h)=
      t*(Real.log (z+h)-Real.log z-halaszLogTaylor k z h) := by ring
  rw [he,abs_mul] at hp
  exact hp.trans (by
    have hh := mul_le_mul_of_nonneg_left (halasz_log_taylor_remainder k hz hh hhz)
      (abs_nonneg t)
    nlinarith)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszShiftAveraging
namespace OAI

/-! Averaging short multiplicative shifts of a one-bounded sequence. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_short_shift_error (f : ℕ → ℂ) (hf : ∀ n,‖f n‖≤1) (N d : ℕ) :
    ‖(∑ n∈range N,f (n+d))-(∑ n∈range N,f n)‖≤2*d := by
  have he : (∑ n∈range N,f (n+d))-(∑ n∈range N,f n)=
      (∑ n∈range d,f (n+N))-(∑ n∈range d,f n) := by
    have h1 := sum_range_add f N d
    have h2 := sum_range_add f d N
    rw [Nat.add_comm d N] at h2
    have hh := h1.symm.trans h2
    simp_rw [Nat.add_comm] at hh ⊢
    linear_combination -hh
  rw [he]
  have h1 : ‖∑ n∈range d,f (n+N)‖≤ d := by
    calc
      _ ≤ ∑ n∈range d,‖f (n+N)‖ := norm_sum_le _ _
      _ ≤ ∑ _n∈range d,(1:ℝ) := sum_le_sum (fun _ _ => hf _)
      _ = _ := by simp
  have h2 : ‖∑ n∈range d,f n‖≤ d := by
    calc
      _ ≤ ∑ n∈range d,‖f n‖ := norm_sum_le _ _
      _ ≤ ∑ _n∈range d,(1:ℝ) := sum_le_sum (fun _ _ => hf _)
      _ = _ := by simp
  exact (norm_sub_le _ _).trans (by linarith)

theorem halasz_double_shift_averaging (f : ℕ → ℂ) (hf : ∀ n,‖f n‖≤1)
    (N M₁ M₂ : ℕ) (B : ℝ)
    (hB : ∀ n∈range N, ‖∑ a : Fin M₁,∑ b : Fin M₂,
      f (n+(a.val+1)*(b.val+1))‖≤ B) :
    ((M₁*M₂:ℕ):ℝ)*‖∑ n∈range N,f n‖≤(N:ℝ)*B+2*((M₁*M₂:ℕ):ℝ)^2 := by
  let S := ∑ n∈range N,f n
  let T := ∑ a : Fin M₁,∑ b : Fin M₂,∑ n∈range N,f (n+(a.val+1)*(b.val+1))
  have he : T=∑ n∈range N,∑ a : Fin M₁,∑ b : Fin M₂,
      f (n+(a.val+1)*(b.val+1)) := by
    calc
      _ = ∑ a : Fin M₁,∑ n∈range N,∑ b : Fin M₂,f (n+(a.val+1)*(b.val+1)) := by
        apply sum_congr rfl
        intro a _
        rw [sum_comm]
      _ = _ := sum_comm
  have hT : ‖T‖≤(N:ℝ)*B := by
    rw [he]
    apply (norm_sum_le _ _).trans
    exact (sum_le_sum hB).trans_eq (by simp)
  have herror : ‖T-((M₁*M₂:ℕ):ℂ)*S‖≤2*((M₁*M₂:ℕ):ℝ)^2 := by
    have he' : T-((M₁*M₂:ℕ):ℂ)*S=
        ∑ a : Fin M₁,∑ b : Fin M₂,((∑ n∈range N,
          f (n+(a.val+1)*(b.val+1)))-S) := by
      simp only [T,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_mul]
      ring
    rw [he']
    apply (norm_sum_le _ _).trans
    apply (sum_le_sum (fun _ _ => norm_sum_le _ _)).trans
    calc
      _ ≤ ∑ _a : Fin M₁,∑ _b : Fin M₂,2*((M₁*M₂:ℕ):ℝ) := by
        apply sum_le_sum
        intro a _
        apply sum_le_sum
        intro b _
        have hh := halasz_short_shift_error f hf N ((a.val+1)*(b.val+1))
        have hab : (a.val+1)*(b.val+1)≤ M₁*M₂ := Nat.mul_le_mul (by omega) (by omega)
        exact hh.trans (by exact_mod_cast Nat.mul_le_mul_left 2 hab)
      _ = _ := by simp [pow_two]; ring
  calc
    _ = ‖((M₁*M₂:ℕ):ℂ)*S‖ := by rw [norm_mul,Complex.norm_natCast]
    _ = ‖T+(((M₁*M₂:ℕ):ℂ)*S-T)‖ := by congr 1; ring
    _ ≤ ‖T‖+‖((M₁*M₂:ℕ):ℂ)*S-T‖ := norm_add_le _ _
    _ = ‖T‖+‖T-((M₁*M₂:ℕ):ℂ)*S‖ := by rw [norm_sub_rev]
    _ ≤ _ := add_le_add hT herror

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogCoefficients
namespace OAI

/-! Identification of the logarithmic Taylor polynomial with the exact
coefficient-torus character in the double mean-value estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Complex




lemma halasz_log_taylor_character (k : ℕ) (t : ℝ) {z : ℝ} (hz : z≠0) (a b : ℕ) :
    halaszVinogradovCharacter (fun j : Fin k => ((a^(j.val+1):ℕ):ℤ))
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => ((b^(j.val+1):ℕ):ℤ)))=
      Complex.exp (Complex.I*((t*halaszLogTaylor k z ((a*b:ℕ):ℝ):ℝ):ℂ)) := by
  have he (j : Fin k) :
      fourier ((a^(j.val+1):ℕ):ℤ)
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => ((b^(j.val+1):ℕ):ℤ)) j)=
      Complex.exp (Complex.I*((t*((-1:ℝ)^j.val*
        (((a*b:ℕ):ℝ)/z)^(j.val+1)/(j.val+1)):ℝ):ℂ)) := by
    dsimp only [halaszScaledFrequency]
    rw [fourier_coe_apply]
    dsimp only [halaszLogCoefficient]
    congr 1
    push_cast
    have hzC : (z:ℂ)≠0 := by exact_mod_cast hz
    have hpiC : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
    simp only [div_pow,mul_pow]
    field_simp [hzC,hpiC]
  unfold halaszVinogradovCharacter
  simp_rw [he]
  rw [← Complex.exp_sum]
  congr 1
  rw [halaszLogTaylor,← Fin.sum_univ_eq_sum_range]
  push_cast
  rw [mul_sum,mul_sum]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogBilinear
namespace OAI

/-! Transfer the logarithmic bilinear sum to its complete-system Taylor
polynomial with an explicit uniform error. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

lemma halasz_log_taylor_phase_factor (k : ℕ) (t : ℝ) {z : ℝ} (hz : z≠0) (a b : ℕ) :
    Complex.exp (Complex.I*((t*(Real.log z+halaszLogTaylor k z ((a*b:ℕ):ℝ)):ℝ):ℂ))=
      Complex.exp (Complex.I*((t*Real.log z:ℝ):ℂ))*
        halaszVinogradovCharacter (fun j : Fin k => ((a^(j.val+1):ℕ):ℤ))
          (halaszScaledFrequency (halaszLogCoefficient t z)
            (fun j => ((b^(j.val+1):ℕ):ℤ))) := by
  rw [halasz_log_taylor_character k t hz,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem halasz_log_bilinear_taylor (k M₁ M₂ : ℕ) (t : ℝ) {z : ℝ}
    (hz : 0< z) (hM : ((M₁*M₂:ℕ):ℝ)≤ z/2) :
    ‖∑ b : Fin M₂,∑ a : Fin M₁,
      Complex.exp (Complex.I*((t*Real.log (z+(a.val+1)*(b.val+1)):ℝ):ℂ))‖≤
      ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖+
        ((M₁*M₂:ℕ):ℝ)*(2*|t| * (((M₁*M₂:ℕ):ℝ)/z)^(k+1)) := by
  let U := ∑ b : Fin M₂,∑ a : Fin M₁,
    Complex.exp (Complex.I*((t*Real.log (z+(a.val+1)*(b.val+1)):ℝ):ℂ))
  let V := ∑ b : Fin M₂,∑ a : Fin M₁,
    Complex.exp (Complex.I*((t*(Real.log z+
      halaszLogTaylor k z (((a.val+1)*(b.val+1):ℕ):ℝ)):ℝ):ℂ))
  have hdiff : ‖U-V‖≤((M₁*M₂:ℕ):ℝ)*(2*|t| * (((M₁*M₂:ℕ):ℝ)/z)^(k+1)) := by
    dsimp only [U,V]
    rw [← sum_sub_distrib]
    simp_rw [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply (sum_le_sum (fun _ _ => norm_sum_le _ _)).trans
    calc
      _ ≤ ∑ _b : Fin M₂,∑ _a : Fin M₁,
          (2*|t| * (((M₁*M₂:ℕ):ℝ)/z)^(k+1)) := by
        apply sum_le_sum
        intro b _
        apply sum_le_sum
        intro a _
        have hab : ((a.val+1)*(b.val+1):ℕ)≤ M₁*M₂ :=
          Nat.mul_le_mul (by omega) (by omega)
        have habR : (((a.val+1)*(b.val+1):ℕ):ℝ)≤((M₁*M₂:ℕ):ℝ) := by exact_mod_cast hab
        have hh := halasz_log_taylor_phase k t hz
          (Nat.cast_nonneg ((a.val+1)*(b.val+1))) (habR.trans hM)
        have hp := pow_le_pow_left₀ (by positivity :
            0≤(((a.val+1)*(b.val+1):ℕ):ℝ)/z)
          (div_le_div_of_nonneg_right habR hz.le) (k+1)
        have hb := mul_le_mul_of_nonneg_left hp (by positivity : 0≤2*|t|)
        simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hh.trans hb
      _ = _ := by simp; ring
  have hV : ‖V‖=‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖ := by
    have he : V=Complex.exp (Complex.I*((t*Real.log z:ℝ):ℂ))*
        (∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
          (halaszScaledFrequency (halaszLogCoefficient t z)
            (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))) := by
      dsimp only [V]
      simp_rw [halasz_log_taylor_phase_factor k t hz.ne']
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      rw [halaszVinogradovPolynomial,mul_sum]
    rw [he,norm_mul,Complex.norm_exp_I_mul_ofReal,one_mul]
  have hn : ‖U‖≤‖V‖+‖U-V‖ := by
    calc
      _ = ‖V+(U-V)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  exact hn.trans (by rw [hV]; exact add_le_add le_rfl hdiff)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogShiftBound
namespace OAI

/-! From a normalized logarithmic polynomial bound to the actual ordinary
exponential sum, with both Taylor and shift-boundary errors retained. -/
namespace TwoPointCorrelations

open _root_.Complex _root_.Finset

theorem halasz_log_shift_bound (k H M : ℕ) (hM : 1≤ M) (t : ℝ)
    {x A : ℝ} (hx : 0< x) (hMx : (M:ℝ)^2≤ x/2)
    (hpoly : ∀ n∈range H,
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency (halaszLogCoefficient t (x+n))
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2≤ A) :
    ‖∑ n∈range H,Complex.exp (Complex.I*((t*Real.log (x+n):ℝ):ℂ))‖≤
      (H:ℝ)*(A+2*|t| *((M:ℝ)^2/x)^(k+1))+2*(M:ℝ)^2 := by
  let f : ℕ → ℂ := fun n => Complex.exp (Complex.I*((t*Real.log (x+n):ℝ):ℂ))
  let T := 2*|t| *((M:ℝ)^2/x)^(k+1)
  have hM0 : 0<(M:ℝ) := by exact_mod_cast (show 0< M by omega)
  have hM2 : 0<(M:ℝ)^2 := sq_pos_of_pos hM0
  have hf : ∀ n,‖f n‖≤1 := by
    intro n
    dsimp only [f]
    rw [Complex.norm_exp_I_mul_ofReal]
  have hB : ∀ n∈range H,‖∑ a : Fin M,∑ b : Fin M,
      f (n+(a.val+1)*(b.val+1))‖≤(M:ℝ)^2*(A+T) := by
    intro n hn
    have hxn : 0< x+n := by positivity
    have hlocal := halasz_log_bilinear_taylor k M M t hxn
      (by push_cast; nlinarith [show (0:ℝ)≤ n by positivity])
    have hp := (div_le_iff₀ hM2).mp (hpoly n hn)
    have hquot : (M:ℝ)^2/(x+n)≤(M:ℝ)^2/x :=
      div_le_div_of_nonneg_left (sq_nonneg _) hx (by linarith [show (0:ℝ)≤ n from Nat.cast_nonneg n])
    have herror := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0≤(M:ℝ)^2/(x+n)) hquot (k+1))
      (by positivity : 0≤2*|t|)
    have heq : (∑ a : Fin M,∑ b : Fin M,f (n+(a.val+1)*(b.val+1)))=
        ∑ b : Fin M,∑ a : Fin M,Complex.exp
          (Complex.I*((t*Real.log ((x+n)+(a.val+1)*(b.val+1)):ℝ):ℂ)) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      dsimp only [f]
      congr 3
      push_cast
      ring_nf
    rw [heq]
    apply hlocal.trans
    push_cast at hp hlocal ⊢
    simp only [← pow_two] at hp hlocal ⊢
    have hE := mul_le_mul_of_nonneg_left herror (sq_nonneg (M:ℝ))
    dsimp only [T] at *
    nlinarith
  have hh := halasz_double_shift_averaging f hf H M M ((M:ℝ)^2*(A+T)) hB
  dsimp only [f] at hh
  apply (mul_le_mul_iff_right₀ hM2).mp
  convert (preTransparency := .instances) hh using 1
  · push_cast
    ring
  · dsimp only [T]
    push_cast
    ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszShortScale
namespace OAI

/-! Integer short-variable lengths for the logarithmic bilinear argument. -/
namespace TwoPointCorrelations


lemma halasz_short_scale_bounds {N α : ℝ} (hN : 1≤ N) (hα : 0≤α) :
    1≤ halaszShortScale N α ∧ N^α≤2*(halaszShortScale N α:ℝ) ∧
      (halaszShortScale N α:ℝ)≤ N^α := by
  have hy : 1≤ N^α := Real.one_le_rpow hN hα
  have hy0 : 0≤ N^α := by linarith
  have hp : 1≤ halaszShortScale N α := (Nat.le_floor_iff hy0).mpr (by exact_mod_cast hy)
  have hpR : 1≤(halaszShortScale N α:ℝ) := by exact_mod_cast hp
  refine ⟨hp,?_,Nat.floor_le hy0⟩
  have hh : N^α<(halaszShortScale N α:ℝ)+1 := Nat.lt_floor_add_one _
  linarith

lemma halasz_short_scale_square {N α : ℝ} (hN : 1≤ N) (hα : 0≤α) :
    (halaszShortScale N α:ℝ)^2≤ N^(2*α) := by
  have hb := (halasz_short_scale_bounds hN hα).2.2
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) hb 2
  convert (preTransparency := .instances) hh using 1
  rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0≤ N)]
  congr 1
  ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTaylorScale
namespace OAI

/-! Taylor remainder at the chosen short-variable scale. -/
namespace TwoPointCorrelations

lemma halasz_taylor_scale {M k : ℕ} {N x t α lam : ℝ}
    (hN : 1≤ N) (hx : N≤ x) (hM : (M:ℝ)^2≤ N^(2*α)) (ht : |t|=N^lam)
    (hexp : lam+(2*α-1)*((k:ℝ)+1)≤-(1/2:ℝ)) :
    2*|t| * ((M:ℝ)^2/x)^(k+1)≤2*N^(-(1/2:ℝ)) := by
  have hN0 : 0< N := by linarith
  have hx0 : 0< x := hN0.trans_le hx
  have hquot : (M:ℝ)^2/x≤ N^(2*α-1) := by
    calc
      _ ≤ N^(2*α)/x := div_le_div_of_nonneg_right hM hx0.le
      _ ≤ N^(2*α)/N := div_le_div_of_nonneg_left
        (Real.rpow_nonneg hN0.le _) hN0 hx
      _ = _ := by rw [Real.rpow_sub hN0,Real.rpow_one]
  have hp := pow_le_pow_left₀ (by positivity : 0≤(M:ℝ)^2/x) hquot (k+1)
  calc
    _ ≤ 2*|t| * (N^(2*α-1))^(k+1) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 2*N^(lam+(2*α-1)*((k:ℝ)+1)) := by
      rw [ht,← Real.rpow_natCast,← Real.rpow_mul hN0.le]
      push_cast
      rw [Real.rpow_add hN0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN hexp) (by norm_num)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseFromPolynomial
namespace OAI

/-! Uniform logarithmic phase prefixes from the normalized polynomial
estimate, with one common boundary error for both short-variable scales. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

theorem halasz_phase_from_polynomial {N H k : ℕ} (hN : 1≤ N) (hH : H≤ N)
    {a t α lam A : ℝ} (ha : a∈Set.Icc (0:ℝ) 1) (hα : 0≤α) (hαhi : α≤1/3)
    (hA : 0≤ A) (hhalf : (N:ℝ)^(2/3:ℝ)≤(N:ℝ)/2) (ht : |t|=(N:ℝ)^lam)
    (htaylor : lam+(2*α-1)*((k:ℝ)+1)≤-(1/2:ℝ))
    (hpoly : ∀ z∈Set.Icc (N:ℝ) (2*N),
      ‖∑ b : Fin (halaszShortScale N α),halaszVinogradovPolynomial k (halaszShortScale N α)
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(halaszShortScale N α:ℝ)^2≤ A) :
    ‖∑ n∈range H,Complex.exp (Complex.I*((t*Real.log ((N:ℝ)+a+n):ℝ):ℂ))‖≤
      (N:ℝ)*A+4*(N:ℝ)^(2/3:ℝ) := by
  have hNR : 1≤(N:ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N:ℝ) := by linarith
  let M := halaszShortScale N α
  have hM := (halasz_short_scale_bounds hNR hα).1
  have hM2 : (M:ℝ)^2≤(N:ℝ)^(2*α) := halasz_short_scale_square hNR hα
  have hM23 : (M:ℝ)^2≤(N:ℝ)^(2/3:ℝ) := hM2.trans
    (Real.rpow_le_rpow_of_exponent_le hNR (by linarith))
  have hMx : (M:ℝ)^2≤((N:ℝ)+a)/2 := by linarith [ha.1]
  have hx : 0<(N:ℝ)+a := by linarith [ha.1]
  have h := halasz_log_shift_bound k H M hM t hx hMx (A := A) (fun n hn => by
    apply hpoly
    have hnN : n+1≤ N := by have := mem_range.mp hn; omega
    have hnNR : (n:ℝ)+1≤ N := by exact_mod_cast hnN
    exact ⟨by linarith [ha.1,show (0:ℝ)≤ n from Nat.cast_nonneg n],by linarith [ha.2]⟩)
  have he := halasz_taylor_scale hNR (show (N:ℝ)≤(N:ℝ)+a by linarith [ha.1]) hM2 ht htaylor
  have hHR : (H:ℝ)≤ N := by exact_mod_cast hH
  have herr : (H:ℝ)*(2*(N:ℝ)^(-(1/2:ℝ)))≤2*(N:ℝ)^(2/3:ℝ) := by
    calc
      _ ≤ (N:ℝ)*(2*(N:ℝ)^(-(1/2:ℝ))) :=
        mul_le_mul_of_nonneg_right hHR (by positivity)
      _ = 2*((N:ℝ)^(1:ℝ)*(N:ℝ)^(-(1/2:ℝ))) := by rw [Real.rpow_one]; ring
      _ = 2*(N:ℝ)^(1/2:ℝ) := by rw [← Real.rpow_add hN0]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hNR (by norm_num : (1/2:ℝ)≤2/3)) (by norm_num)
  apply h.trans
  have hmain := mul_le_mul_of_nonneg_right hHR hA
  have herror := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg H)
  nlinarith

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_phase_from_polynomial := @OAI.TwoPointCorrelations.halasz_phase_from_polynomial
