-- Prove2me | solution 1 for LogLogJam.Supplement.squeezed_phase_density_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:27:06.095488+00:00
-- url     : https://prove2.me/submissions/bc829461-159a-43e5-b1c3-d3962f0f805c

import Mathlib
open Filter MeasureTheory Complex
open scoped ENNReal Topology ComplexConjugate
set_option maxHeartbeats 700000
private noncomputable def b (n : ℕ) : ℝ := Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n
private theorem bn (n : ℕ) : 0 ≤ b n := by unfold b; positivity
private theorem b0 : b 0 = 1 := by norm_num [b,Nat.centralBinom]
private theorem b_rec (n : ℕ) : b (n+1) = Real.sqrt (((n:ℝ)+1/2)/(n+1))*b n := by
  have hc : ((n:ℝ)+1)*((n+1).centralBinom:ℝ) = 2*(2*(n:ℝ)+1)*(n.centralBinom:ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have h1 : 0 ≤ ((n:ℝ)+1/2)/(n+1) := by positivity
  have h : (b (n+1))^2 = (Real.sqrt (((n:ℝ)+1/2)/(n+1))*b n)^2 := by
    simp only [b,mul_pow,div_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt h1, pow_succ (n:=n)]
    field_simp; nlinarith
  exact (sq_eq_sq₀ (bn _) (mul_nonneg (Real.sqrt_nonneg _) (bn _))).mp h
private theorem bd (n : ℕ) : b (n+1) ≤ b n := by
  rw [b_rec]
  apply mul_le_of_le_one_left (bn _)
  apply (Real.sqrt_le_iff.mpr ⟨zero_le_one,?_⟩)
  rw [one_pow]; exact (div_le_one (by positivity)).mpr (by linarith)
private theorem b1 (n : ℕ) : b n ≤ 1 := (antitone_nat_of_succ_le bd (Nat.zero_le _)).trans_eq b0
private noncomputable def a (n : ℕ) := Ring.multichoose (3/4:ℝ) n
private theorem a_rec (n : ℕ) : a (n+1) = (((n:ℝ)+3/4)/(n+1))*a n := by
  have ha := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (3/4:ℝ) n
  have hb := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (3/4:ℝ) (n+1)
  rw [ascPochhammer_succ_right,Polynomial.smeval_mul,Polynomial.smeval_add,Polynomial.smeval_X,← ha] at hb
  have ev : (n : Polynomial ℕ).smeval (3/4:ℝ) = n := by rw [← Polynomial.C_eq_natCast,Polynomial.smeval_C]; simp
  simp only [nsmul_eq_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,ev,pow_one] at hb
  change (↑n+1)*(n.factorial:ℝ)*a (n+1) = (n.factorial:ℝ)*a n*(3/4 + ↑n) at hb
  field_simp
  apply mul_left_cancel₀ (show (n.factorial:ℝ)≠0 by positivity)
  linear_combination 4*hb
private theorem a0 : a 0 = 1 := by simp [a,Ring.multichoose_zero_right]
private theorem a_pos (n : ℕ) : 0 < a n := by
  induction n with
  | zero => rw [a0]; norm_num
  | succ n ih => rw [a_rec]; positivity
private theorem a_bound (n : ℕ) : a n ≤ 2*b (n+1) := by
  induction n with
  | zero => rw [a0, b_rec 0, b0]; norm_num; field_simp; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg 2]
  | succ n ih =>
    have hr : ((n:ℝ)+3/4)/(n+1) ≤ Real.sqrt ((((n:ℝ)+1)+1/2)/(n+1+1)) := by
      apply Real.le_sqrt_of_sq_le
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
      field_simp
      nlinarith
    rw [a_rec,b_rec (n+1),Nat.cast_add_one]
    calc
      _ ≤ Real.sqrt ((((n:ℝ)+1)+1/2)/(n+1+1)) * (2*b (n+1)) :=
        mul_le_mul hr ih (a_pos _).le (Real.sqrt_nonneg _)
      _ = _ := by ring
private theorem a_series (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    HasSum (fun n : ℕ => a n*q^n) (1/(1-q)^(3/4:ℝ)) := by
  have hb : q ∈ Metric.eball 0 1 := by
    simpa [Metric.mem_eball,edist_dist,Real.norm_eq_abs,abs_of_nonneg hq] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hq).mpr hq'
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (3/4)).hasSum hb
  have H (n : ℕ) : Ring.choose ((3/4:ℝ) + n - 1) n = a n := by
    rw [Ring.choose,show (3/4:ℝ) + n - 1 - n + 1 = 3/4 by ring]; rfl
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,H,smul_eq_mul,zero_add] using h
private theorem b_sum (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    Summable fun n : ℕ => b n*q^n := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (bn _) (pow_nonneg hq _)) _ (summable_geometric_of_lt_one hq hq')
  intro n; exact mul_le_of_le_one_left (pow_nonneg hq _) (b1 _)
private theorem peak (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    1/(1-q)^(3/4:ℝ) ≤ 2* ∑' n : ℕ, b n*q^n := by
  rw [← (a_series q hq hq').tsum_eq,← tsum_mul_left]
  apply (a_series q hq hq').summable.tsum_le_tsum _ ((b_sum q hq hq').mul_left 2)
  intro n
  calc
    _ ≤ (2*b n)*q^n := mul_le_mul_of_nonneg_right ((a_bound n).trans (by gcongr; exact bd n)) (pow_nonneg hq n)
    _ = _ := by ring
private theorem n_sum (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    Summable fun n : ℕ => (n:ℝ)*(b n*q^n) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hq] using hq'
  have h : Summable fun n : ℕ => (n:ℝ)*q^n := by simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (bn _) (pow_nonneg hq _))) _ h
  intro n; gcongr; exact mul_le_of_le_one_left (pow_nonneg hq _) (b1 n)
private theorem moment (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    (1-q)*(∑' n : ℕ, (n:ℝ)*(b n*q^n)) ≤ ∑' n : ℕ, b n*q^n := by
  let X (n : ℕ) := b n*q^n
  let Y (n : ℕ) := (n:ℝ)*X n
  have hX : Summable X := b_sum q hq hq'
  have hY : Summable Y := n_sum q hq hq'
  have h : (∑' n, Y n) ≤ q * ((∑' n, Y n) + ∑' n, X n) := by
    calc
      (∑' n, Y n) = ∑' n : ℕ, Y (n+1) := by
        rw [hY.tsum_eq_zero_add]; dsimp [Y]; simp
      _ ≤ ∑' n : ℕ, q * (Y n + X n) := by
        apply ((summable_nat_add_iff 1).2 hY).tsum_le_tsum _ ((hY.add hX).mul_left q)
        intro n; dsimp [X,Y]; rw [Nat.cast_succ,pow_succ]
        calc
          _ ≤ ((n:ℝ)+1) * (b n * (q^n*q)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (bd n) (by positivity)) (by positivity)
          _ = _ := by ring
      _ = _ := by rw [tsum_mul_left, (hY.tsum_add hX)]
  change (1-q)*(∑' n, Y n) ≤ ∑' n, X n
  have hpos : 0 ≤ ∑' n, X n := tsum_nonneg fun n => mul_nonneg (bn _) (pow_nonneg hq _)
  nlinarith [mul_le_mul_of_nonneg_right hq'.le hpos]
private noncomputable def amp (q t : ℝ) := ∑' n : ℕ, (b n*q^n:ℝ) * Complex.exp (Complex.I*((-((n:ℝ)*t)):ℝ))
private theorem ampSum (q t : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    Summable fun n : ℕ => (b n*q^n:ℝ) * Complex.exp (Complex.I*((-((n:ℝ)*t)):ℝ)) := by
  apply (b_sum q hq hq').of_norm_bounded
  intro n; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (bn _) (pow_nonneg hq _)),
    Complex.norm_exp_I_mul_ofReal,mul_one]
private theorem near (q t : ℝ) (hq : 0 ≤ q) (hq' : q < 1) (ht : |t| ≤ (1-q)/2) :
    1/(1-q)^(3/4:ℝ) ≤ 4*‖amp q t‖ := by
  let X (n : ℕ) := b n*q^n
  let W (n : ℕ) := Complex.exp (Complex.I*((-((n:ℝ)*t)):ℝ))
  let U := ∑' n, X n
  let V := ∑' n : ℕ, (n:ℝ)*X n
  have nX n : 0 ≤ X n := mul_nonneg (bn _) (pow_nonneg hq _)
  have nU : 0 ≤ U := tsum_nonneg nX
  have nV : 0 ≤ V := tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (nX _)
  have hV : (1-q)*V ≤ U := moment q hq hq'
  have hdiff : ‖amp q t - (U:ℂ)‖ ≤ V*|t| := by
    have hX : Summable X := b_sum q hq hq'
    have hW : Summable fun n : ℕ => (X n:ℂ)*W n := ampSum q t hq hq'
    have hD n : ‖(X n:ℂ)*W n - (X n:ℂ)‖ ≤ ((n:ℝ)*X n)*|t| := by
      rw [← mul_sub_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (nX n)]
      have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x:=-((n:ℝ)*t))
      rw [Real.norm_eq_abs,abs_neg,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)] at he
      calc
        _ ≤ X n * ((n:ℝ)*|t|) := mul_le_mul_of_nonneg_left he (nX n)
        _ = _ := by ring
    change ‖(∑' n, (X n:ℂ)*W n) - ((∑' n, X n):ℝ)‖ ≤ (∑' n : ℕ, (n:ℝ)*X n)*|t|
    rw [Complex.ofReal_tsum, ← hW.tsum_sub (Complex.summable_ofReal.mpr hX),← tsum_mul_right]
    have hZ := (n_sum q hq hq').mul_right |t|
    have hN := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hD hZ
    exact (norm_tsum_le_tsum_norm hN).trans (hN.tsum_le_tsum hD hZ)
  have hn : U - ‖amp q t‖ ≤ ‖amp q t - (U:ℂ)‖ := by
    have h := norm_sub_norm_le (U:ℂ) (amp q t)
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg nU,norm_sub_rev] using h
  have hp : 1/(1-q)^(3/4:ℝ) ≤ 2*U := peak q hq hq'
  nlinarith [mul_le_mul_of_nonneg_left ht nV]
private theorem far (q t : ℝ) (hq : 0 ≤ q) (hq' : q < 1) (ht : Real.cos t ≤ 0) : ‖amp q t‖ ≤ 2 := by
  let z := (q:ℂ) * Complex.exp (Complex.I*(-(t:ℂ)))
  let f (n : ℕ) := (b n:ℂ)*z^n
  let X (n : ℕ) := b n*q^n
  let G := ∑' n, f n
  let U := ∑' n, X n
  have hz : ‖z‖=q := by simp [z,norm_mul, Complex.norm_exp, Real.norm_eq_abs,abs_of_nonneg hq]
  have hn n : ‖f n‖=X n := by simp [f,X,norm_mul,hz,Real.norm_eq_abs,abs_of_nonneg (bn n)]
  have hX : Summable X := b_sum q hq hq'
  have hf : Summable f := hX.of_norm_bounded fun n => (hn n).le
  have h0n : 0 ≤ U := tsum_nonneg fun n => mul_nonneg (bn _) (pow_nonneg hq _)
  have haG : amp q t = G := by
    apply tsum_congr; intro n
    simp only [f,z,mul_pow, Complex.ofReal_mul,Complex.ofReal_pow,← Complex.exp_nat_mul,
      ← mul_assoc]
    congr 1
    push_cast; ring_nf
  have hG : G = 1 + ∑' n : ℕ, f (n+1) := by simpa [G,f,b0] using hf.tsum_eq_zero_add
  have hU : U = 1 + ∑' n : ℕ, X (n+1) := by simpa [U,X,b0] using hX.tsum_eq_zero_add
  let D (n : ℕ) := f n*z - f (n+1)
  let d (n : ℕ) := X n*q - X (n+1)
  have hnD n : ‖D n‖ = d n := by
    have he : D n = ((b n-b (n+1):ℝ):ℂ)*z^(n+1) := by simp [D,f,pow_succ]; ring
    rw [he,norm_mul,norm_pow,hz,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (bd n))]
    dsimp [d,X]; rw [pow_succ]; ring
  have hd : Summable d := (hX.mul_right q).sub ((summable_nat_add_iff 1).2 hX)
  have hsum : (∑' n : ℕ, d n) = q*U -(U-1) := by
    change (∑' n : ℕ, (X n*q - X (n+1))) = _
    rw [(hX.mul_right q).tsum_sub ((summable_nat_add_iff 1).2 hX),tsum_mul_right]
    change U*q - _ = _; linarith
  have hsumD : (∑' n : ℕ, D n) = G*z - (G-1) := by
    change (∑' n : ℕ, (f n*z - f (n+1))) = _
    rw [(hf.mul_right z).tsum_sub ((summable_nat_add_iff 1).2 hf),tsum_mul_right]
    change G*z - _ = _
    linear_combination hG
  have hd1 : ‖∑' n : ℕ, D n‖ ≤ 1 := by
    have H : Summable fun n => ‖D n‖ := by simpa only [hnD] using hd
    apply (norm_tsum_le_tsum_norm H).trans
    simp_rw [hnD]; rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_right hq'.le h0n]
  have h2 : ‖(1-z)*G‖ ≤ 2 := by
    have he : (1-z)*G = 1-∑' n : ℕ, D n := by rw [hsumD]; ring
    rw [he]; simpa using (norm_sub_le (1:ℂ) (∑' n, D n)).trans (by rw [norm_one]; linarith)
  have hre : 1 ≤ ‖1-z‖ := by
    have he : (1-z).re = 1-q*Real.cos t := by
      have e : Complex.I*(-(t:ℂ)) = ((-t:ℝ):ℂ)*Complex.I := by push_cast; ring
      simp only [z,e,Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
        Complex.exp_ofReal_mul_I_re,Real.cos_neg]
    exact (by rw [he]; nlinarith [mul_nonpos_of_nonneg_of_nonpos hq ht] : 1 ≤ (1-z).re).trans (Complex.re_le_norm _)
  rw [haG]
  calc
    _ ≤ ‖1-z‖*‖G‖ := le_mul_of_one_le_left (norm_nonneg _) hre
    _ ≤ 2 := by simpa only [norm_mul] using h2
theorem solution (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    let A := fun t : ℝ => ∑' n : ℕ,
      (((Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n)*q^n:ℝ):ℂ) *
        Complex.exp (Complex.I*((-((n:ℝ)*t)):ℝ))
    let p := fun t : ℝ => Real.sqrt (1-q^2)/(2*Real.pi) * ‖A t‖^2
    (∀ t : ℝ, |t| ≤ (1-q)/2 → 1/(32*Real.pi) ≤ (1-q)*p t) ∧
    (∀ t : ℝ, Real.cos t ≤ 0 → p t ≤ 2*Real.sqrt (1-q^2)/Real.pi) := by
  have hd : 0 < 1-q := by linarith
  have hroot : Real.sqrt (1-q) ≤ Real.sqrt (1-q^2) := Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hq'.le hq])
  have hpi := Real.pi_pos
  constructor
  · intro t ht
    let w := (1-q)^(3/4:ℝ)
    have hw : 0 < w := Real.rpow_pos_of_pos hd _
    have h := near q t hq hq' ht
    have h1 : 1 ≤ 4*‖amp q t‖*w := (div_le_iff₀ hw).mp h
    have h2 : 1 ≤ (4*‖amp q t‖*w)^2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) h1]
    have hw2 : w^2 = (1-q)*Real.sqrt (1-q) := by
      dsimp [w]; rw [← Real.rpow_two,← Real.rpow_mul hd.le, show (3/4:ℝ)*2 = 1 + 1/2 by norm_num,
        Real.rpow_add hd, Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [mul_pow,hw2] at h2
    change 1/(32*Real.pi) ≤ (1-q)*(Real.sqrt (1-q^2)/(2*Real.pi)*‖amp q t‖^2)
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg hd.le (sq_nonneg ‖amp q t‖))]
  · intro t ht
    have h := far q t hq hq' ht
    have h2 := mul_self_le_mul_self (norm_nonneg _) h
    change Real.sqrt (1-q^2)/(2*Real.pi)*‖amp q t‖^2 ≤ 2*Real.sqrt (1-q^2)/Real.pi
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (1-q^2))]
