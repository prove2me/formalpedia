-- Prove2me | solution 1 for MasulloAudit.exponential_schwartz_mellin_zero_count_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:50:41.012622+00:00
-- url     : https://prove2.me/submissions/c0e8749e-5c70-4bff-a576-dbbad6f7be1a

import Mathlib

section
open MeasureTheory Set Polynomial
open scoped SchwartzMap ContDiff

noncomputable section
namespace MasulloBox

private lemma polynomial_exp_bound (p : ℂ[X]) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, ‖p.eval (x : ℂ)‖ ≤ K * Real.exp |x| := by
  induction p using Polynomial.induction_on' with
  | monomial n a =>
    refine ⟨‖a‖ * (n.factorial : ℝ), by positivity, ?_⟩
    intro x
    simp only [Polynomial.eval_monomial, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hp := (div_le_iff₀ (show 0 < (n.factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n)
    calc
      _ ≤ ‖a‖ * (Real.exp |x| * n.factorial) := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = _ := by ring
  | add p q hp hq =>
    obtain ⟨K, hK, hp⟩ := hp
    obtain ⟨L, hL, hq⟩ := hq
    refine ⟨K+L, by positivity, fun x => ?_⟩
    rw [Polynomial.eval_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hp x) (hq x))

private lemma exponential_polynomial_derivative (q : ℂ[X]) (n : ℕ) :
    ∃ p : ℂ[X], iteratedDeriv n (fun x : ℝ => Complex.exp (q.eval (x : ℂ))) =
      fun x : ℝ => p.eval (x : ℂ) * Complex.exp (q.eval (x : ℂ)) := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.derivative+p*q.derivative, ?_⟩
    rw [iteratedDeriv_succ, hp]
    funext x
    have h := ((p.hasDerivAt (x : ℂ)).mul ((q.hasDerivAt (x : ℂ)).cexp)).comp_ofReal
    convert h.deriv using 1 <;> simp [Polynomial.eval_add, Polynomial.eval_mul]; ring

private lemma quadratic_schwartz (b c : ℂ) (hb : b.re < 0) :
    ∃ g : 𝓢(ℝ,ℂ), ∀ x : ℝ, g x = Complex.exp (b*x^2 + c*x) := by
  let q : ℂ[X] := C b * X^2 + C c * X
  have hq (x : ℝ) : q.eval (x : ℂ) = b*x^2+c*x := by simp [q]
  let g : ℝ → ℂ := fun x => Complex.exp (q.eval (x : ℂ))
  have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hg : ContDiff ℝ ∞ g := by dsimp [g]; simp_rw [hq]; fun_prop
  refine ⟨⟨g,hg,?_⟩,fun x => by change Complex.exp (q.eval _) = _; rw [hq]⟩
  intro k n
  obtain ⟨p,hp⟩ := exponential_polynomial_derivative q n
  obtain ⟨K,hK,hP⟩ := polynomial_exp_bound (X^k*p)
  let L : ℝ := 1+|c.re|
  refine ⟨K*Real.exp (L^2/(-4*b.re)),fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖x‖^k * ‖iteratedDeriv n (fun x : ℝ => Complex.exp (q.eval (x : ℂ))) x‖ ≤ _
  rw [hp, norm_mul, ← mul_assoc, Real.norm_eq_abs]
  have hpx := hP x
  simp [Polynomial.eval_mul, norm_pow, Real.norm_eq_abs] at hpx
  have hreal : (q.eval (x : ℂ)).re = b.re*x^2+c.re*x := by
    rw [hq, ← Complex.ofReal_pow]; simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hquad : |x| + (b.re*x^2+c.re*x) ≤ L^2/(-4*b.re) := by
    have hcx := (le_abs_self (c.re*x)).trans_eq (abs_mul _ _)
    apply (le_div_iff₀ (by linarith : 0 < -4*b.re)).mpr
    have hlin : |x|+(b.re*x^2+c.re*x) ≤ b.re*x^2+L*|x| := by dsimp [L]; linarith
    apply (mul_le_mul_of_nonneg_right hlin (by linarith : 0 ≤ -4*b.re)).trans
    nlinarith [sq_nonneg (2*b.re*|x|+L), sq_abs x,
      show b.re^2*|x|^2 = b.re^2*x^2 by rw [sq_abs]]
  rw [Complex.norm_exp, hreal]
  calc
    _ ≤ K * Real.exp |x| * Real.exp (b.re*x^2+c.re*x) :=
      mul_le_mul_of_nonneg_right hpx (Real.exp_nonneg _)
    _ = K * Real.exp (|x|+(b.re*x^2+c.re*x)) := by rw [Real.exp_add |x| _]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad) hK



private lemma hasMellin_log_equiv (f : ℝ → ℂ) (s y : ℂ) :
    HasMellin (fun t : ℝ => f (Real.log t)) s y ↔
      Integrable (fun x : ℝ => Complex.exp (s*x) * f x) ∧
      (∫ x : ℝ, Complex.exp (s*x) * f x) = y := by
  have hder : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have himage : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have hkey (x : ℝ) : |Real.exp x| • (((Real.exp x : ℝ) : ℂ) ^ (s-1) • f (Real.log (Real.exp x))) =
      Complex.exp (s*x) * f x := by
    rw [abs_of_pos (Real.exp_pos _), Real.log_exp, Complex.real_smul, smul_eq_mul,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_nonneg _), Real.log_exp, Complex.ofReal_exp, ← mul_assoc,
      ← Complex.exp_add]
    congr 2; ring
  unfold HasMellin MellinConvergent mellin
  rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ hder Real.exp_injective.injOn,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder Real.exp_injective.injOn]
  simp only [hkey, integrableOn_univ, setIntegral_univ]

private def quadCoeff (c : ℂ) := -(4*c)⁻¹
private def quadNormal (c : ℂ) := ((Real.pi:ℂ) / (-quadCoeff c)) ^ (1/2:ℂ)
private def quadTest (c : ℂ) (x : ℝ) := (quadNormal c)⁻¹ * Complex.exp (quadCoeff c*x^2)

private lemma quadCoeff_re_neg {c : ℂ} (hc : 0 < c.re) : (quadCoeff c).re < 0 := by
  simp [quadCoeff, Complex.inv_re, Complex.mul_re]
  exact div_pos hc (Complex.normSq_pos.mpr (fun h => by simp [h] at hc))

private lemma quadTest_hasMellin {c : ℂ} (hc : 0 < c.re) (s : ℂ) :
    HasMellin (fun t : ℝ => quadTest c (Real.log t)) s (Complex.exp (c*s^2)) := by
  rw [hasMellin_log_equiv]
  have hb := quadCoeff_re_neg hc
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hb0 : quadCoeff c ≠ 0 := fun h => by simp [h] at hb
  have hnorm : quadNormal c ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (neg_ne_zero.mpr hb0)
  have he (x : ℝ) : Complex.exp (s*x)*quadTest c x =
      (quadNormal c)⁻¹ * Complex.exp (quadCoeff c*x^2 + s*x + 0) := by
    dsimp [quadTest]; rw [add_zero, Complex.exp_add]; ring
  simp_rw [he]
  refine ⟨(integrable_cexp_quadratic' hb s 0).const_mul _, ?_⟩
  rw [integral_const_mul, integral_cexp_quadratic hb, ← mul_assoc]
  change (quadNormal c)⁻¹ * quadNormal c * _ = _
  rw [inv_mul_cancel₀ hnorm, one_mul]
  congr 1
  dsimp [quadCoeff]; field_simp; ring

private lemma weighted_quadTest {c : ℂ} (hc : 0 < c.re) (a : ℝ) :
    ∃ g : 𝓢(ℝ,ℂ), ∀ x : ℝ, g x = Complex.exp ((a:ℂ)*x) * quadTest c x := by
  obtain ⟨g,hg⟩ := quadratic_schwartz (quadCoeff c) (a : ℂ) (quadCoeff_re_neg hc)
  refine ⟨(quadNormal c)⁻¹ • g,fun x => ?_⟩
  change (quadNormal c)⁻¹ * g x = _
  rw [hg, Complex.exp_add]; dsimp [quadTest]; ring

/-- An exponentially Schwartz test on the positive norm line whose Mellin transform has
equally spaced squared zero ordinates. All real exponential tilts are Schwartz in log coordinates. -/
theorem exists_exponentialSchwartz_mellin_counterexample :
    ∃ φ : ℝ → ℂ,
      (∀ a : ℝ, ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = Complex.exp ((a : ℂ) * x) * φ (Real.exp x)) ∧
      ∀ s : ℂ, HasMellin φ s
        (Complex.exp (s ^ 2) * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * s ^ 2) - 1)) := by
  let c : ℂ := 1+2*(Real.pi:ℂ)*Complex.I
  have hc : 0 < c.re := by simp [c, Complex.mul_re, Complex.mul_im]
  have h1 : 0 < (1:ℂ).re := by simp
  refine ⟨fun t => quadTest c (Real.log t) - quadTest 1 (Real.log t), ?_, ?_⟩
  · intro a
    obtain ⟨g,hg⟩ := weighted_quadTest hc a
    obtain ⟨h,hh⟩ := weighted_quadTest h1 a
    exact ⟨g-h,fun x => by change g x - h x = _; simp only [hg, hh, Real.log_exp, mul_sub]⟩
  · intro s
    have h₁ := quadTest_hasMellin hc s
    have h₂ := quadTest_hasMellin h1 s
    have h := hasMellin_sub h₁.1 h₂.1
    rw [h₁.2, h₂.2, one_mul] at h
    convert h using 2
    rw [show c*s^2 = s^2+2*(Real.pi:ℂ)*Complex.I*s^2 by dsimp [c]; ring, Complex.exp_add]
    ring

end MasulloBox
end
end

section
open Set Filter
open scoped Topology Asymptotics

namespace MasulloAudit.BoxZeros
noncomputable section

def chirp (z : ℂ) : ℂ := Complex.exp (z^2) * (Complex.exp (2 * Real.pi * Complex.I * z^2)-1)

theorem chirp_zero_iff (z : ℂ) : chirp z = 0 ↔ ∃ k : ℤ, z^2 = (k : ℂ) := by
  rw [chirp,mul_eq_zero,or_iff_right (Complex.exp_ne_zero _),sub_eq_zero,Complex.exp_eq_one_iff]
  have ha : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨k,h⟩
    exact ⟨k,mul_left_cancel₀ ha (h.trans (mul_comm _ _))⟩
  · rintro ⟨k,h⟩
    exact ⟨k,by rw [h,mul_comm]⟩

theorem chirp_ne_zero : chirp ≠ 0 := by
  intro h
  have h0 : chirp (1+Complex.I)=0 := congrFun h _
  obtain ⟨k,hk⟩ := (chirp_zero_iff _).mp h0
  have := congrArg Complex.im hk
  norm_num [pow_two,Complex.mul_im] at this

private def root (k : ℕ) : ℂ := (Real.sqrt (k:ℝ) : ℂ) * Complex.I

private lemma root_re (k : ℕ) : (root k).re = 0 := by simp [root,Complex.mul_re]
private lemma root_im (k : ℕ) : (root k).im = Real.sqrt k := by simp [root,Complex.mul_im]

private lemma root_sq (k : ℕ) : (root k)^2 = -(k:ℂ) := by
  rw [root,mul_pow,Complex.I_sq,← Complex.ofReal_pow,Real.sq_sqrt (Nat.cast_nonneg k)]
  simp

private lemma root_injective : Function.Injective root := by
  intro a b h
  have he := congrArg (fun z : ℂ => z^2) h
  simpa only [root_sq,neg_inj,Nat.cast_inj] using he

/-- All distinct zeros in the closed height-one rectangle, including its endpoints. -/
theorem exact_closed_box (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Finset ℂ, s.card = 2*n+2 ∧ ∀ z : ℂ, z ∈ s ↔
      chirp z=0 ∧ z.re ∈ Icc (-1:ℝ) 1 ∧ z.im ∈ Icc (n:ℝ) ((n:ℝ)+1) := by
  classical
  let e : ℕ ↪ ℂ := ⟨root,root_injective⟩
  let S := (Finset.Icc (n^2) ((n+1)^2)).map e
  refine ⟨S,?_,?_⟩
  · simp only [S,Finset.card_map,Nat.card_Icc]
    have he : (n+1)^2 = n^2+2*n+1 := by ring
    omega
  · intro z
    constructor
    · intro hz
      obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨ha,hb⟩ := Finset.mem_Icc.mp hk
      change chirp (root k) = 0 ∧ _ ∧ _
      refine ⟨(chirp_zero_iff _).2 ⟨-(k:ℤ),by simpa using root_sq k⟩,?_,?_⟩
      · change (root k).re ∈ _
        rw [root_re]; norm_num
      · change (root k).im ∈ _
        rw [root_im]
        have h₁ : (n:ℝ)^2 ≤ (k:ℝ) := by exact_mod_cast ha
        have h₂ : (k:ℝ) ≤ ((n:ℝ)+1)^2 := by exact_mod_cast hb
        exact ⟨(Real.sqrt_sq (Nat.cast_nonneg n)) ▸ Real.sqrt_le_sqrt h₁,
          (Real.sqrt_sq (by positivity : 0 ≤ (n:ℝ)+1)) ▸ Real.sqrt_le_sqrt h₂⟩
    · rintro ⟨hz,_,ha,hb⟩
      have him : 0 < z.im := lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_of_lt hn) ha
      obtain ⟨k,hk⟩ := (chirp_zero_iff z).mp hz
      have hi := congrArg Complex.im hk
      simp only [pow_two,Complex.mul_im,Complex.intCast_im] at hi
      have hprod : z.re*z.im=0 := by nlinarith only [hi]
      have hre : z.re=0 := (mul_eq_zero.mp hprod).resolve_right him.ne'
      have hreal := congrArg Complex.re hk
      simp only [pow_two,Complex.mul_re,Complex.intCast_re,hre,zero_mul,zero_sub] at hreal
      have hy : z.im^2 = -(k:ℝ) := by nlinarith only [hreal]
      have hk0 : 0 ≤ -k := by exact_mod_cast (show 0 ≤ -(k:ℝ) from hy ▸ sq_nonneg _)
      let m := (-k).toNat
      have hmk : (m:ℤ) = -k := Int.toNat_of_nonneg hk0
      have hm : (m:ℝ)=z.im^2 := by
        rw [hy]
        exact_mod_cast hmk
      have hma : n^2 ≤ m := by
        exact_mod_cast (show (n:ℝ)^2 ≤ (m:ℝ) by rw [hm]; nlinarith [sq_nonneg (z.im-n)])
      have hmb : m ≤ (n+1)^2 := by
        exact_mod_cast (show (m:ℝ) ≤ ((n:ℝ)+1)^2 by rw [hm]; nlinarith [sq_nonneg ((n:ℝ)+1-z.im)])
      refine Finset.mem_map.mpr ⟨m,Finset.mem_Icc.mpr ⟨hma,hmb⟩,?_⟩
      apply Complex.ext
      · exact (root_re m).trans hre.symm
      · change (root m).im = z.im
        rw [root_im, hm, Real.sqrt_sq him.le]

/-- For every logarithmic constant and every lower cutoff, a later closed
rectangle contains more distinct zeros than the proposed bound. -/
theorem arbitrarily_large_closed_box (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ ∃ s : Finset ℂ,
      (∀ z : ℂ, z ∈ s ↔ chirp z=0 ∧ z.re ∈ Icc (-1:ℝ) 1 ∧ z.im ∈ Icc (n:ℝ) ((n:ℝ)+1)) ∧
      C * Real.log n < (s.card : ℝ) := by
  have hlim : Tendsto (fun n : ℕ => C*(Real.log n/(n:ℝ))) atTop (𝓝 0) := by
    have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
    simpa only [Function.comp_def,pow_one,one_mul,add_zero,mul_zero] using ht.const_mul C
  have ht : ∀ᶠ n : ℕ in atTop, N ≤ n ∧ 1 ≤ n ∧ C*(Real.log n/(n:ℝ)) < 1 :=
    (eventually_ge_atTop N).and ((eventually_ge_atTop 1).and (hlim.eventually_lt_const (by norm_num)))
  obtain ⟨n,hn,h1,h⟩ := ht.exists
  obtain ⟨s,hcard,hs⟩ := exact_closed_box n h1
  refine ⟨n,hn,h1,s,hs,?_⟩
  have hn0 : (0:ℝ)<n := by exact_mod_cast Nat.zero_lt_of_lt h1
  rw [←mul_div_assoc,div_lt_iff₀ hn0,one_mul] at h
  rw [hcard]
  push_cast
  linarith

/-- The literal closed rectangle in the vertical strip with real part between −1 and 1. -/
def zerosAtHeight (F : ℂ → ℂ) (T : ℝ) : Set ℂ :=
  {z | F z=0 ∧ z.re ∈ Icc (-1:ℝ) 1 ∧ z.im ∈ Icc T (T+1)}

abbrev zerosInBox (F : ℂ → ℂ) (n : ℕ) : Set ℂ := zerosAtHeight F n

theorem exact_zero_count (n : ℕ) (hn : 1 ≤ n) :
    (zerosInBox chirp n).Finite ∧ (zerosInBox chirp n).ncard = 2*n+2 := by
  obtain ⟨s,hcard,hs⟩ := exact_closed_box n hn
  have he : zerosInBox chirp n = (s : Set ℂ) := Set.ext fun z => (hs z).symm
  rw [he,Set.ncard_coe_finset,hcard]
  exact ⟨s.finite_toSet,rfl⟩

theorem box_count_not_isBigO :
    ¬ (fun n : ℕ => ((zerosInBox chirp n).ncard : ℝ)) =O[atTop] (fun n : ℕ => Real.log n) := by
  intro hO
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨N,hN⟩ := eventually_atTop.mp hC
  obtain ⟨n,hn,h1,s,hs,h⟩ := arbitrarily_large_closed_box C N
  have he : zerosInBox chirp n = (s : Set ℂ) := Set.ext fun z => (hs z).symm
  have hB := hN n hn
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast h1)
  simp only [he,Set.ncard_coe_finset,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) s.card),abs_of_nonneg hlog] at hB
  exact h.not_ge hB

theorem real_box_count_not_isBigO :
    ¬ (fun T : ℝ => ((zerosAtHeight chirp T).ncard : ℝ)) =O[atTop] (fun T : ℝ => Real.log |T|) := by
  intro h
  apply box_count_not_isBigO
  simpa only [Function.comp_def,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _)] using
    h.comp_tendsto (tendsto_natCast_atTop_atTop (R:=ℝ))

theorem differentiable_chirp : Differentiable ℂ chirp := by
  unfold chirp
  fun_prop

end
end MasulloAudit.BoxZeros
end

open Set Filter MeasureTheory
open scoped SchwartzMap Asymptotics Topology

theorem solution :
    ∃ φ : ℝ → ℂ,
      (∀ a : ℝ, ∃ g : 𝓢(ℝ,ℂ), ∀ x : ℝ,
        g x = Complex.exp ((a:ℂ)*x) * φ (Real.exp x)) ∧
      (∀ z : ℂ, HasMellin φ z
        (Complex.exp (z^2) * (Complex.exp (2*(Real.pi:ℂ)*Complex.I*z^2)-1))) ∧
      mellin φ ≠ 0 ∧
      (∀ n : ℕ, 1 ≤ n → ∃ S : Finset ℂ, S.card = 2*n+2 ∧ ∀ z : ℂ,
        z ∈ S ↔ mellin φ z = 0 ∧ z.re ∈ Icc (-1:ℝ) 1 ∧ z.im ∈ Icc (n:ℝ) ((n:ℝ)+1)) ∧
      ¬ (fun T : ℝ => (({z : ℂ | mellin φ z = 0 ∧ z.re ∈ Icc (-1:ℝ) 1 ∧
          z.im ∈ Icc T (T+1)} : Set ℂ).ncard : ℝ)) =O[atTop] (fun T : ℝ => Real.log |T|) := by
  obtain ⟨φ,hφ,hM⟩ := MasulloBox.exists_exponentialSchwartz_mellin_counterexample
  have he : mellin φ = MasulloAudit.BoxZeros.chirp := funext fun z => (hM z).2
  refine ⟨φ,hφ,hM,?_,?_,?_⟩
  · rw [he]
    exact MasulloAudit.BoxZeros.chirp_ne_zero
  · rw [he]
    exact MasulloAudit.BoxZeros.exact_closed_box
  · rw [he]
    exact MasulloAudit.BoxZeros.real_box_count_not_isBigO
