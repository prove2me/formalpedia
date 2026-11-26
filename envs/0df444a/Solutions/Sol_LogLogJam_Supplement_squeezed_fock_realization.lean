-- Prove2me | solution 1 for LogLogJam.Supplement.squeezed_fock_realization
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:21:59.219601+00:00
-- url     : https://prove2.me/submissions/7ab1d09d-3130-498e-b610-eac1dd7379ac

import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Theorems.Thm_BosonicLearn_gaussianAt_of_characteristic
import Theorems.Thm_BosonicLearn_husimi_fourier
import Theorems.Thm_BosonicLearn_isDensity_of_posSemidef
open LogLogJam LogLogJam.Supplement BosonicLearn Matrix MeasureTheory
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix

open Filter MeasureTheory Matrix BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal Topology BigOperators
set_option maxHeartbeats 240000

private theorem middle_coef (n : ℕ) : Ring.multichoose (1/2:ℂ) n = (n.centralBinom : ℂ)/4^n := by
  induction n with
  | zero => simp [Nat.centralBinom, Ring.multichoose_zero_right]
  | succ n ih =>
    have ha := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1/2:ℂ) n
    have hb := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1/2:ℂ) (n+1)
    rw [ascPochhammer_succ_right,Polynomial.smeval_mul,Polynomial.smeval_add,Polynomial.smeval_X,← ha] at hb
    simp [nsmul_eq_mul,Nat.factorial_succ,ih] at hb
    have hnat : ((n:ℂ)+1) * ((n+1).centralBinom : ℂ) = 2*(2*(n:ℂ)+1)*(n.centralBinom:ℂ) := by exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hfac : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [pow_succ]
    have ev : (n : Polynomial ℕ).smeval (1/2:ℂ) = n := by rw [← Polynomial.C_eq_natCast,Polynomial.smeval_C]; simp
    field_simp at hb
    rw [ev,ih] at hb
    field_simp at hb
    apply (eq_div_iff (by norm_num)).mpr
    apply (mul_left_cancel₀ hn)
    linear_combination 2*hb - hnat

private theorem center_series (z : ℂ) (hz : ‖z‖ < 1) : HasSum (fun n : ℕ =>
    ((n.centralBinom:ℂ)/4^n) * z^n) (1/(1-z)^(1/2:ℂ)) := by
  have hb : z ∈ Metric.eball 0 1 := by simpa [Metric.mem_eball,edist_dist] using (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z)).mpr hz
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (1/2)).hasSum hb
  have H (n : ℕ) : Ring.choose ((1/2:ℂ) + n - 1) n = (n.centralBinom:ℂ)/4^n := by
    rw [Ring.choose,show (1/2:ℂ) + n - 1 - n + 1 = 1/2 by ring,middle_coef]
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,H,smul_eq_mul,zero_add] using h
@[irreducible] private noncomputable def wAmp (r θ : ℝ) (n : ℕ) : ℂ :=
  if Even n then ((Real.sqrt ((n/2).centralBinom : ℝ) / ((2:ℝ)^(n/2) * Real.sqrt (Real.cosh r)) : ℝ) : ℂ) *
    ((Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ) * Complex.I))^(n/2) else 0

private theorem sq_n (r θ : ℝ) (j : ℕ) : ‖wAmp r θ (2*j)‖^2 =
    1/Real.cosh r * ((j.centralBinom:ℝ)/4^j * (Real.tanh r ^ 2)^j) := by
  have c := (Real.cosh_pos r).le
  simp only [wAmp, even_two_mul, if_true, Nat.mul_div_cancel_left _ (by decide : 0<2),norm_mul,norm_pow,
    Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs, mul_pow, ← Nat.pow_mul, ← sq_abs,
    sq_abs, div_pow,Real.sq_sqrt c,Real.sq_sqrt (Nat.cast_nonneg _)]
  have h : |Real.tanh r| ^ (j*2) = Real.tanh r ^ (j*2) := by rw [Nat.mul_comm, pow_mul, sq_abs, ← pow_mul]
  ring_nf; rw [h, show ((2:ℝ)⁻¹)^(j*2) = (4⁻¹:ℝ)^j by rw [Nat.mul_comm, pow_mul]; norm_num]

private theorem tanh_gap (r : ℝ) : 1 - Real.tanh r ^2 = (Real.cosh r ^ 2)⁻¹ := by
  rw [Real.tanh_eq_sinh_div_cosh]; field_simp [(Real.cosh_pos r).ne']; nlinarith [Real.cosh_sq_sub_sinh_sq r]

private theorem center_sum_real (r : ℝ) : HasSum (fun j : ℕ => (j.centralBinom:ℝ)/4^j * (Real.tanh r ^ 2)^j) (Real.cosh r) := by
  let q := Real.tanh r ^ 2
  have hq : 0 ≤ q := sq_nonneg _
  have hlt : q < 1 := by have h := tanh_gap r; have h' := inv_pos.mpr (sq_pos_of_pos (Real.cosh_pos r)); unfold q; linarith
  have h := center_series (q:ℂ) (by simpa [abs_of_nonneg hq] using hlt)
  have he : 1 / (1 - (q:ℂ))^(1/2:ℂ) = (Real.cosh r : ℂ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow (sub_nonneg.mpr hlt.le)]
    change 1 / (( (1-q)^(1/2:ℝ) : ℝ) : ℂ) = _
    rw [← Real.sqrt_eq_rpow,show 1-q = _ from tanh_gap r, Real.sqrt_inv,Real.sqrt_sq (Real.cosh_pos r).le]
    simp
  rw [he] at h
  have hc := Complex.reCLM.hasSum h
  simpa only [← Complex.ofReal_natCast,← Complex.ofReal_ofNat,← Complex.ofReal_pow,← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.reCLM_apply,Complex.ofReal_re,q] using hc

private theorem amp_normalized (r θ : ℝ) : HasSum (fun n : ℕ => ‖wAmp r θ n‖^2) 1 := by
  have he : HasSum (fun j : ℕ => ‖wAmp r θ (2*j)‖^2) 1 := by
    simp_rw [sq_n]
    simpa [(Real.cosh_pos r).ne'] using (center_sum_real r).mul_left (1/Real.cosh r)
  have ho : HasSum (fun j : ℕ => ‖wAmp r θ (2*j+1)‖^2) 0 := by simpa [wAmp] using (hasSum_zero : HasSum (fun _ : ℕ => (0:ℝ)) 0)
  simpa using HasSum.even_add_odd (f:=fun n => ‖wAmp r θ n‖^2) he ho

private theorem rank_density {I : Type} [Countable I] (w : I → ℂ) (hn : HasSum (fun i => ‖w i‖^2) 1) :
    IsDensity (fun i j => w i * star (w j)) := by
  classical
  have d (i) : (w i * star (w i)).re = ‖w i‖^2 := by simp [Complex.mul_conj',← Complex.ofReal_pow]
  apply isDensity_of_posSemidef _ _ (by simpa only [d] using hn.summable) (by simpa only [d] using hn.tsum_eq)
  intro s z
  let v := ∑ i ∈ s, star (z i) * w i
  have he : (∑ i ∈ s, ∑ j ∈ s, star (z i) * (w i * star (w j)) * z j) = v * star v := by
    simp only [v,star_sum,star_mul',star_star,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  rw [he,Complex.star_def,Complex.mul_conj']; norm_cast; exact ⟨rfl,sq_nonneg _⟩


private theorem sum_over_fock {M : Type} [AddCommMonoid M] [TopologicalSpace M] {f : ℕ → M} {a : M}
    (h : HasSum f a) : HasSum (fun u : Fin 1 → ℕ => f (u 0)) a := by
  let e : ℕ ≃ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm
  exact (e.hasSum_iff (f := fun u : Fin 1 → ℕ => f (u 0))).mp h

private theorem state_of_amp (r θ : ℝ) : ∃ ρ : State (Occupation (Fin 1)),
    ∀ u v, ρ.coefficients u v = wAmp r θ (u 0) * star (wAmp r θ (v 0)) := by
  have h : HasSum (fun u : Fin 1 → ℕ => ‖wAmp r θ (u 0)‖^2) 1 := sum_over_fock (amp_normalized r θ)
  let v : (Fin 1 → ℕ) → ℂ := fun u => wAmp r θ (u 0)
  let X : Matrix (Fin 1 → ℕ) (Fin 1 → ℕ) ℂ := fun u j => v u * star (v j)
  have hd : IsDensity X := rank_density (I := (Fin 1 → ℕ)) v h
  let ρ : State (Fin 1 → ℕ) := ⟨X, hd⟩
  exact ⟨ρ,fun _ _ => rfl⟩

private noncomputable def coAmp (x y : ℝ) (n : ℕ) : ℂ :=
  ((Real.exp (-(x^2+y^2)/4) : ℝ) : ℂ) *
    ((x:ℂ)+Complex.I*(y:ℂ))^n / ((Real.sqrt 2 : ℂ)^n * (Real.sqrt n.factorial : ℂ))

private theorem fac_even (j : ℕ) :
    Real.sqrt ((2*j).factorial:ℝ) = Real.sqrt (j.centralBinom:ℝ) * j.factorial := by
  have hnat : (2*j).factorial = j.centralBinom*j.factorial*j.factorial := by
    simpa only [Nat.centralBinom,two_mul] using (Nat.add_choose_mul_factorial_mul_factorial j j).symm
  rw [hnat,Nat.cast_mul,Nat.cast_mul,mul_assoc,← sq,Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]

private theorem overlap_term (r θ x y : ℝ) (j : ℕ) :
    star (coAmp x y (2*j)) * wAmp r θ (2*j) =
      (((Real.exp (-(x^2+y^2)/4) / Real.sqrt (Real.cosh r) : ℝ) : ℂ)) *
        (((Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ)*Complex.I)) *
           ((x:ℂ)-Complex.I*(y:ℂ))^2 / 4)^j / j.factorial := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by norm_cast; norm_num
  have hc : (Real.sqrt (j.centralBinom:ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.centralBinom_pos j))).ne'
  simp only [coAmp,wAmp,even_two_mul,if_true,Nat.mul_div_cancel_left _ (by decide : 0<2),
    star_div₀,star_mul',star_pow,star_add,Complex.star_def,Complex.conj_ofReal,Complex.conj_I,
    fac_even,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat]
  rw [pow_mul,pow_mul,hs]
  simp only [← sub_eq_add_neg,neg_mul,div_pow,mul_pow]
  have h2 : (4:ℂ)^j = 2^j * 2^j := by rw [← mul_pow]; norm_num
  rw [h2]
  simp only [map_natCast]
  field_simp
  <;> ring

private theorem overlap_sum (r θ x y : ℝ) : HasSum (fun n : ℕ => star (coAmp x y n) * wAmp r θ n)
    ((((Real.exp (-(x^2+y^2)/4) / Real.sqrt (Real.cosh r) : ℝ) : ℂ)) *
      Complex.exp (((Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ)*Complex.I)) *
                     ((x:ℂ)-Complex.I*(y:ℂ))^2 / 4)) := by
  let c : ℂ := ((Real.exp (-(x^2+y^2)/4) / Real.sqrt (Real.cosh r) : ℝ) : ℂ)
  let a : ℂ := ((Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ)*Complex.I)) * ((x:ℂ)-Complex.I*(y:ℂ))^2 / 4
  have he : HasSum (fun j : ℕ => star (coAmp x y (2*j)) * wAmp r θ (2*j)) (c * Complex.exp a) := by
    simp_rw [overlap_term]; simpa only [c,a,Complex.exp_eq_exp_ℂ,mul_div_assoc] using (NormedSpace.expSeries_div_hasSum_exp a).mul_left c
  have ho : HasSum (fun j : ℕ => star (coAmp x y (2*j+1)) * wAmp r θ (2*j+1)) 0 := by
    simpa [wAmp] using (hasSum_zero : HasSum (fun _ : ℕ => (0:ℂ)) 0)
  simpa only [add_zero] using HasSum.even_add_odd (f:=fun n => star (coAmp x y n) * wAmp r θ n) he ho
private theorem rankQ (r θ : ℝ) (ρ : State (Occupation (Fin 1)))
    (hρ : ∀ u v, ρ.coefficients u v = wAmp r θ (u 0) * star (wAmp r θ (v 0)))
    (β : Fin 1 ⊕ Fin 1 → ℝ) :
    husimiQ ρ.coefficients β =
      let x := β (.inl 0)
      let y := β (.inr 0)
      let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ) * Complex.I)
      (2 * Real.pi)⁻¹ *
      ‖((Real.exp (-(x^2+y^2)/4) / Real.sqrt (Real.cosh r) : ℝ) : ℂ) *
           Complex.exp (z*((x:ℂ)-Complex.I*(y:ℂ))^2 / 4)‖^2 := by
  dsimp only
  let f (u : Fin 1 → ℕ) := star (coherentVector β u) * wAmp r θ (u 0)
  let A : ℂ := (((Real.exp (-(β (.inl 0)^2+β (.inr 0)^2)/4) / Real.sqrt (Real.cosh r) : ℝ) : ℂ)) *
      Complex.exp (((Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ)*Complex.I)) *
                     ((β (.inl 0):ℂ)-Complex.I*(β (.inr 0):ℂ))^2 / 4)
  have co (u : Fin 1 → ℕ) : coherentVector β u = coAmp (β (.inl 0)) (β (.inr 0)) (u 0) := by
    simp only [coherentVector,Fin.prod_univ_one,coAmp]
  have hf : HasSum f A := by
    simp only [f,co,A]
    exact sum_over_fock (overlap_sum r θ _ _)
  have he (u v : Fin 1 → ℕ) : star (coherentVector β u) * ρ.coefficients u v * coherentVector β v =
       f u * star (f v) := by rw [hρ]; simp only [f,star_mul',star_star]; ring
  have hsum : (∑' u, ∑' v, star (coherentVector β u) * ρ.coefficients u v * coherentVector β v) = A * star A := by
    simp_rw [he, fun u => (hf.star.mul_left (f u)).tsum_eq]
    exact (hf.mul_right (star A)).tsum_eq
  unfold husimiQ
  rw [hsum,Complex.star_def,Complex.mul_conj']
  rw [← Complex.ofReal_pow,Complex.ofReal_re]
  change _ * ‖A‖^2 = _ * ‖A‖^2
  rw [Nat.cast_one,Real.rpow_neg_one]
private theorem real_husimi (r θ : ℝ) (ρ : State (Occupation (Fin 1)))
    (hρ : ∀ u v, ρ.coefficients u v = wAmp r θ (u 0) * star (wAmp r θ (v 0))) (β : Fin 1 ⊕ Fin 1 → ℝ) :
    husimiQ ρ.coefficients β =
      let x := β (.inl 0)
      let y := β (.inr 0)
      let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ) * Complex.I)
      (2 * Real.pi * Real.cosh r)⁻¹ *
      Real.exp (-(1-z.re)/2*x^2 + z.im*x*y - (1+z.re)/2*y^2) := by
  let x := β (Sum.inl 0)
  let y := β (Sum.inr 0)
  let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ) * Complex.I)
  rw [rankQ _ _ _ hρ]; dsimp only
  change (2 * Real.pi)⁻¹ *
      ‖((Real.exp (-(x^2+y^2)/4) / Real.sqrt (Real.cosh r) : ℝ) : ℂ) * Complex.exp (z*((x:ℂ)-Complex.I*(y:ℂ))^2/4)‖^2 =
       _ * Real.exp (-(1-z.re)/2*x^2+z.im*x*y-(1+z.re)/2*y^2)
  have he : (z*((x:ℂ)-Complex.I*(y:ℂ))^2/4).re =
      (z.re*(x^2-y^2)+2*z.im*x*y)/4 := by
    simp [Complex.div_ofNat_re,pow_two,Complex.mul_re,Complex.mul_im]; ring
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,Real.sq_sqrt (Real.cosh_pos r).le,
    Complex.norm_exp,he,← Real.exp_nat_mul,← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  rw [show (2*Real.pi)⁻¹ * (Real.exp (2*(-(x^2+y^2)/4)) / Real.cosh r * Real.exp (2*((z.re*(x^2-y^2)+2*z.im*x*y)/4))) =
    (2*Real.pi*Real.cosh r)⁻¹ * (Real.exp (2*(-(x^2+y^2)/4)) * Real.exp (2*((z.re*(x^2-y^2)+2*z.im*x*y)/4))) by ring,← Real.exp_add]
  congr 2; ring
open MeasureTheory Complex
open scoped Topology
set_option maxHeartbeats 300000

private theorem pos_sqrtC (u : ℝ) (hu : 0 ≤ u) : ((u:ℂ)^(1/2:ℂ)) = ((Real.sqrt u:ℝ):ℂ) := by
  rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow hu]; norm_num

private noncomputable def wave (A B D m n : ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp ((-(D:ℂ)/2) * (p.2:ℂ)^2 +
     ((B:ℂ)*(p.1:ℂ)+Complex.I*(n:ℂ))*(p.2:ℂ) +
     (-(A:ℂ)/2*(p.1:ℂ)^2 + Complex.I*(m:ℂ)*(p.1:ℂ)))

private theorem plane (A B D m n : ℝ) (hD : 0 < D) (hdet : 0 < A*D-B^2)
    (hInt : Integrable (wave A B D m n)) :
    ∫ p : ℝ × ℝ, wave A B D m n p =
      ((2*Real.pi/Real.sqrt (A*D-B^2) : ℝ):ℂ) *
        Complex.exp ((-(D*m^2+2*B*m*n+A*n^2)/(2*(A*D-B^2)):ℝ):ℂ) := by
  let P := A*D-B^2
  have hP : 0 < P := hdet
  have dC : (D:ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have pC : (P:ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hb : (-(D:ℂ)/2).re < 0 := by simpa using (by linarith : -D/2 < 0)
  have ha : ((-(P:ℂ)/(2*(D:ℂ)))).re < 0 := by
    rw [← Complex.ofReal_neg,show (2:ℂ)*(D:ℂ)=((2*D:ℝ):ℂ) by push_cast; rfl, ← Complex.ofReal_div,Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hP) (by positivity)
  have hI : Complex.I^2 = -1 := Complex.I_sq
  have e1 (x : ℝ) : (-(A:ℂ)/2*(x:ℂ)^2 + Complex.I*(m:ℂ)*(x:ℂ)) -
      ((B:ℂ)*(x:ℂ)+Complex.I*(n:ℂ))^2/(4*(-(D:ℂ)/2)) =
      (-(P:ℂ)/(2*(D:ℂ)))*(x:ℂ)^2 + (Complex.I*((m:ℂ)+(B:ℂ)*n/D))*(x:ℂ) + (-(n:ℂ)^2 / (2*(D:ℂ))) := by
    dsimp [P]; push_cast; field_simp [dC]; ring_nf; rw [Complex.I_sq]; ring
  have e2 : (-(n:ℂ)^2/(2*(D:ℂ))) - (Complex.I*((m:ℂ)+(B:ℂ)*n/D))^2/(4*(-(P:ℂ)/(2*(D:ℂ)))) =
      ((-(D*m^2+2*B*m*n+A*n^2)/(2*(A*D-B^2)):ℝ):ℂ) := by
    push_cast
    rw [show (A:ℂ)*D-(B:ℂ)^2=(P:ℂ) by dsimp [P]; push_cast; rfl,mul_pow,hI]
    field_simp [dC,pC]; dsimp [P]; push_cast; ring
  rw [Measure.volume_eq_prod] at hInt ⊢
  rw [integral_prod _ hInt]
  simp only [wave,integral_cexp_quadratic hb,e1,integral_const_mul,integral_cexp_quadratic ha,e2,← mul_assoc]
  congr 1
  have h1 : (Real.pi:ℂ) / -(-(D:ℂ)/2) = ((2*Real.pi/D : ℝ):ℂ) := by push_cast; ring
  have h2 : (Real.pi:ℂ) / -(-(P:ℂ)/(2*(D:ℂ))) = ((2*Real.pi*D/P : ℝ):ℂ) := by push_cast; field_simp
  rw [h1,h2,pos_sqrtC _ (by positivity),pos_sqrtC _ (by positivity),← Complex.ofReal_mul]
  norm_cast
  rw [← Real.sqrt_mul (by positivity),show 2*Real.pi/D*(2*Real.pi*D/P) = (2*Real.pi)^2/P by field_simp]
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (by positivity)]

private noncomputable def xyE : (Fin 1 ⊕ Fin 1 → ℝ) ≃ᵐ (ℝ × ℝ) :=
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 1 ⊕ Fin 1 => ℝ)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 1)).symm).trans (MeasurableEquiv.funUnique (Fin 1) (ℝ × ℝ))

private theorem xy_mp : MeasurePreserving xyE volume volume :=
  ((volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 1 ⊕ Fin 1 => ℝ)).trans
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 1)).symm).trans
      (volume_preserving_funUnique (Fin 1) (ℝ × ℝ))

private theorem husimi_transform (ρ : State (Occupation (Fin 1)))
    (A B D c : ℝ) (hd : 0 < D) (hp : 0 < A*D-B^2) (hc : c ≠ 0)
    (hh : ∀ β : Fin 1 ⊕ Fin 1 → ℝ, husimiQ ρ.coefficients β =
      c * Real.exp (-A/2*β (.inl 0)^2 + B*β (.inl 0)*β (.inr 0) -D/2*β (.inr 0)^2))
    (t : Fin 1 ⊕ Fin 1 → ℝ) :
    let m := t (.inl 0)
    let n := t (.inr 0)
    (∫ β : Fin 1 ⊕ Fin 1 → ℝ, Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ):ℂ)) *
        (husimiQ ρ.coefficients β:ℂ)) =
      ((c*(2*Real.pi/Real.sqrt (A*D-B^2)):ℝ):ℂ) *
        Complex.exp ((-(D*m^2+2*B*m*n+A*n^2)/(2*(A*D-B^2)):ℝ):ℂ) := by
  let m := t (Sum.inl 0)
  let n := t (Sum.inr 0)
  let ϕ (β : Fin 1 ⊕ Fin 1 → ℝ) := Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ):ℂ))
  let F := wave A B D m n
  have hEq (β : Fin 1 ⊕ Fin 1 → ℝ) : ϕ β * (husimiQ ρ.coefficients β:ℂ) = (c:ℂ) * F (xyE β) := by
    change _ = _ * wave A B D m n (β (.inl 0),β (.inr 0))
    rw [hh,Complex.ofReal_mul,Complex.ofReal_exp]
    rw [mul_left_comm,← Complex.exp_add]
    congr 2
    simp [ϕ,m,n,Fintype.sum_sum_type,Fin.sum_univ_one,wave]
    <;> ring
  have hraw : Integrable (fun β => ϕ β * (husimiQ ρ.coefficients β:ℂ)) := by
    have h0 := (husimi_fourier ρ).2.2.2.1
    have hϕ : Continuous ϕ := by dsimp [ϕ]; fun_prop
    have hm := hϕ.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable h0.aestronglyMeasurable)
    apply h0.norm.mono' hm
    filter_upwards with β
    change ‖ϕ β * (husimiQ ρ.coefficients β:ℂ)‖ ≤ ‖husimiQ ρ.coefficients β‖
    rw [norm_mul,show ‖ϕ β‖ = 1 by dsimp [ϕ]; rw [mul_comm,Complex.norm_exp_ofReal_mul_I],one_mul,Complex.norm_real]
  have hF : Integrable F := by
    apply (xy_mp.integrable_comp_emb xyE.measurableEmbedding).mp
    refine ((hraw.const_mul ((c:ℂ)⁻¹)).congr (Filter.Eventually.of_forall fun β => ?_))
    change (c:ℂ)⁻¹ * (ϕ β * (husimiQ ρ.coefficients β:ℂ)) = F (xyE β)
    rw [hEq,← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hc),one_mul]
  change (∫ β, ϕ β * (husimiQ ρ.coefficients β:ℂ)) = _
  simp_rw [hEq,integral_const_mul,xy_mp.integral_comp' F]
  rw [show ∫ p, F p = _ from plane A B D m n hd hp hF]
  push_cast; ring
private noncomputable def Kz (z : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => z
private noncomputable def precisionGap (z : ℂ) : ℝ := 1 - Complex.normSq z
private noncomputable def ga (z : ℂ) (i j : Fin 2) : ℝ :=
  if i = 0 then (if j = 0 then 2*(1+z.re)/precisionGap z - 1 else 2*z.im/precisionGap z)
  else (if j = 0 then 2*z.im/precisionGap z else 2*(1-z.re)/precisionGap z - 1)

private theorem vk_entries {z : ℂ} (hz : ‖z‖ < 1) (i j : Fin 2) :
    VK (Kz z) (i,0) (j,0) = ga z i j := by
  let k := precisionGap z
  have hk : 0 < k := by dsimp [k,precisionGap]; rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have hc : starRingEnd ℂ z * z = (Complex.normSq z:ℂ) := by rw [mul_comm, Complex.mul_conj]
  have h1 : 1-(Kz z)ᴴ*Kz z = (k:ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i; fin_cases j
    simp [Kz,k,precisionGap,Matrix.mul_apply,hc]
  have h2 : 1-Kz z*(Kz z)ᴴ = (k:ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i; fin_cases j
    simp [Kz,k,precisionGap,Matrix.mul_apply,Complex.mul_conj]
  have hi : ((k:ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ))⁻¹ = (k⁻¹:ℝ) • (1:Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i; fin_cases j
    simp [Matrix.inv_def,det_fin_one,adjugate_fin_one,Ring.inverse_eq_inv]
  have hq (i j : Fin 1) : ((Kz z)ᴴ*Kz z) i j = (Complex.normSq z : ℂ) := by
    fin_cases i;fin_cases j;simp [Kz,Matrix.mul_apply,hc]
  unfold VK; rw [h1,h2,hi]
  fin_cases i <;> fin_cases j <;> simp [ga,Matrix.mul_apply,hq,Kz,k,Complex.mul_re,Complex.mul_im]
  all_goals dsimp [k,precisionGap] at *; field_simp; try rw [Complex.normSq_apply]
  all_goals ring

private theorem physical (r θ : ℝ) (hr : 0 ≤ r) (ρ : State (Occupation (Fin 1)))
    (hρ : ∀ u v, ρ.coefficients u v = wAmp r θ (u 0) * star (wAmp r θ (v 0))) : squeezedAt ρ r θ := by
  let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ) * Complex.I)
  let A := 1-z.re
  let B := z.im
  let D := 1+z.re
  let P := precisionGap z
  let c := (2*Real.pi*Real.cosh r)⁻¹
  have hz' : ‖z‖ = |Real.tanh r| := by dsimp only [z]; rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hz : ‖z‖ < 1 := by rw [hz']; exact abs_lt.mpr ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩
  have hD : 0 < D := by have := (abs_le.mp (Complex.abs_re_le_norm z)).1; dsimp [D]; linarith
  have hP : A*D-B^2 = P := by simp [A,D,B,P,precisionGap,Complex.normSq_apply]; ring
  have hgap : P = (Real.cosh r^2)⁻¹ := by dsimp [P,precisionGap]; rw [← Complex.sq_norm,hz',sq_abs,tanh_gap]
  have hdet : 0 < A*D-B^2 := by rw [hP,hgap]; positivity
  have hsqrt : Real.sqrt (A*D-B^2) = (Real.cosh r)⁻¹ := by rw [hP,hgap,Real.sqrt_inv,Real.sqrt_sq (Real.cosh_pos r).le]
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hnorm : c*(2*Real.pi/Real.sqrt (A*D-B^2)) = 1 := by rw [hsqrt]; dsimp [c]; field_simp
  have hh : ∀ β : Fin 1 ⊕ Fin 1 → ℝ, husimiQ ρ.coefficients β =
      c * Real.exp (-A/2*β (.inl 0)^2 + B*β (.inl 0)*β (.inr 0) -D/2*β (.inr 0)^2) := real_husimi r θ ρ hρ
  let Γ : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℝ := fun i j => ga z i.2 j.2
  have hsym : Γ.transpose = Γ := by
    ext ⟨i,j⟩ ⟨k,l⟩; fin_cases j <;> fin_cases l <;> rfl
  have hG : GaussianAt ρ.coefficients 0 Γ := by
    apply gaussianAt_of_characteristic _ _ _ hsym
    intro ξ
    let t : Fin 1 ⊕ Fin 1 → ℝ := Sum.elim (fun j => ξ (j,0)) (fun j => ξ (j,1))
    let m := ξ (0,0)
    let n := ξ (0,1)
    have ht : (fun a : Fin 1 × Fin 2 => if a.2 = 0 then t (.inl a.1) else t (.inr a.1)) = ξ := by
      funext ⟨i,j⟩; fin_cases j <;> rfl
    have htt : ∑ a, t a^2 = m^2+n^2 := by simp [t,m,n,Fintype.sum_sum_type,Fin.sum_univ_one]
    have hw : -(D*m^2+2*B*m*n+A*n^2)/(2*(A*D-B^2)) = -(m^2+n^2)/4 + -varianceForm Γ ξ/4 := by
      rw [hP]
      simp only [varianceForm,Fintype.sum_prod_type,Fin.sum_univ_one,Fin.sum_univ_two,Γ,ga,if_true,↓reduceIte]
      change _ = -(m^2+n^2)/4 + -(m*(2*(1+z.re)/P-1)*m + m*(2*z.im/P)*n +
        (n*(2*z.im/P)*m + n*(2*(1-z.re)/P-1)*n))/4
      dsimp [D,A,B]; field_simp [show P ≠ 0 by rw [← hP]; exact hdet.ne']; ring
    have h := (husimi_fourier ρ).2.2.2.2 t
    rw [ht,htt,husimi_transform ρ A B D c hD hdet hc hh t] at h
    change ((c*(2*Real.pi/Real.sqrt (A*D-B^2)):ℝ):ℂ) * Complex.exp ((-(D*m^2+2*B*m*n+A*n^2)/(2*(A*D-B^2)):ℝ):ℂ) = _ at h
    rw [hnorm,Complex.ofReal_one,one_mul,hw,Complex.ofReal_add,Complex.exp_add,← Complex.ofReal_exp] at h
    have ne : ((Real.exp (-(m^2+n^2)/4):ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    have h' := (mul_left_cancel₀ ne h).symm
    simpa [meanForm] using h'
  refine ⟨hr,?_⟩
  unfold IsGaussQP IsGaussianState
  let q (a : Fin 1 × Fin 2) : Fin 1 ⊕ Fin 1 := if a.2 = 0 then .inl a.1 else .inr a.1
  change GaussianAt ρ.coefficients (fun a => qpVec 0 (q a)) (fun a b =>
    2 * ((1/2:ℝ) • qpMat (VK (Kz z))) (q a) (q b))
  have hμ : (fun a => qpVec 0 (q a)) = (0 : Fin 1 × Fin 2 → ℝ) := by
    funext ⟨a,i⟩; fin_cases i <;> rfl
  have hCov : (fun a b => 2 * ((1/2:ℝ) • qpMat (VK (Kz z))) (q a) (q b)) = Γ := by
    funext ⟨a,i⟩ ⟨b,j⟩; fin_cases a; fin_cases b; fin_cases i <;> fin_cases j <;>
      simp [q,Γ,qpMat,qpIdx,vk_entries hz]
  rw [hμ,hCov]; exact hG

theorem solution (r θ : ℝ) (hr : 0 ≤ r) :
    let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ) * Complex.I)
    let w := fun n : ℕ => if Even n then
      ((Real.sqrt (Nat.centralBinom (n/2) : ℝ) / ((2:ℝ)^(n/2) * Real.sqrt (Real.cosh r)) : ℝ) : ℂ) * z^(n/2) else 0
    ∃ ρ : State (Occupation (Fin 1)), squeezedAt ρ r θ ∧
      ∀ u v, ρ.coefficients u v = w (u 0) * star (w (v 0)) := by
  obtain ⟨ρ,hρ⟩ := state_of_amp r θ
  refine ⟨ρ, physical r θ hr ρ hρ, ?_⟩
  simpa only [wAmp] using hρ
