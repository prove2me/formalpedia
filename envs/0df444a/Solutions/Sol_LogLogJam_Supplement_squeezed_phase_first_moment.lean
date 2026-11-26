-- Prove2me | solution 1 for LogLogJam.Supplement.squeezed_phase_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:28:22.231802+00:00
-- url     : https://prove2.me/submissions/bbd67586-cd91-4d83-97bb-215b0953e0aa

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
private theorem b_sum (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    Summable fun n : ℕ => b n*q^n := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (bn _) (pow_nonneg hq _)) _ (summable_geometric_of_lt_one hq hq')
  intro n; exact mul_le_of_le_one_left (pow_nonneg hq _) (b1 _)

private theorem swapSum (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ℕ → ℝ → ℂ) (g : ℕ → ℝ)
    (hg : Summable g) (hu : ∀ i, Continuous (u i)) (h : ∀ i x, ‖u i x‖ ≤ g i) :
    (∑' n, ∫ x, u n x ∂μ) = ∫ x, ∑' n, u n x ∂μ := by
  apply HasSum.tsum_eq
  apply hasSum_integral_of_dominated_convergence (fun i _ => g i)
    (fun i => (hu i).aestronglyMeasurable) (fun i => ae_of_all _ (h i))
    (ae_of_all _ fun _ => hg) (integrable_const _)
  apply ae_of_all
  intro x
  exact (hg.of_norm_bounded (fun n => h n x)).hasSum

private noncomputable def wave (n : ℕ) (x : ℝ) : ℂ := Complex.exp (-(n:ℂ)*(x:ℂ)*Complex.I)
private theorem wave_norm (n : ℕ) (x : ℝ) : ‖wave n x‖=1 := by simp [wave,Complex.norm_exp]
private theorem wave_cont (n : ℕ) : Continuous (wave n) := by unfold wave; fun_prop
private theorem wave_pair (i j : ℕ) (x : ℝ) :
    star (wave i x) * wave j x = Complex.exp (Complex.I * (((i:ℝ)-j)*x)) := by
  simp only [wave,Complex.star_def, ← Complex.exp_conj, map_mul, map_neg, map_natCast,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_natCast]
  congr 1; ring

private noncomputable def P : ℝ := 2*Real.pi
private def J := Set.Ico 0 P
private theorem ppos : 0 < P := mul_pos (by norm_num) Real.pi_pos
private theorem orth (n : ℤ) :
    (∫ x in J, Complex.exp ((n : ℂ)*Complex.I*(x:ℂ))) = if n=0 then (P:ℂ) else 0 := by
  rw [J,integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le ppos.le]
  by_cases hn : n=0
  · simp [hn]
  · have hc : (n:ℂ)*Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc,if_neg hn]
    have he : (n:ℂ)*Complex.I*(P:ℂ) = n*(2*Real.pi*Complex.I) := by dsimp [P]; push_cast; ring
    rw [he,Complex.exp_int_mul_two_pi_mul_I]; simp

private theorem fourier_autocorrelation (c : ℕ → ℂ) (hc : Summable fun n => ‖c n‖) (m : ℕ) :
    (∫ x in J, star (wave m x) * ((‖∑' n, c n*wave n x‖^2:ℝ):ℂ)) =
      (P:ℂ) * ∑' n, c (n+m) * star (c n) := by
  let μ : Measure ℝ := volume.restrict J
  haveI : IsFiniteMeasure μ := ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  let F := fun i x => c i * wave i x
  let G := fun x => ∑' n, F n x
  let H := fun i x => star (wave m x) * star (F i x)
  have hF i : Continuous (F i) := continuous_const.mul (wave_cont _)
  have hH i : Continuous (H i) := (wave_cont m).star.mul (hF i).star
  have hn i x : ‖F i x‖ = ‖c i‖ := by simp [F,wave_norm]
  have hhn i x : ‖H i x‖ = ‖c i‖ := by simp [H,wave_norm,hn]
  have hG : Continuous G := continuous_tsum hF hc fun i x => (hn i x).le
  have hGn x : ‖G x‖ ≤ ∑' n, ‖c n‖ := by
    calc
      _ ≤ ∑' n, ‖F n x‖ := norm_tsum_le_tsum_norm (by simpa only [hn] using hc)
      _ = _ := tsum_congr fun i => hn i x
  have hstep (i j : ℕ) : (∫ x, H i x * F j x ∂μ) =
      (if j=i+m then (P:ℂ) else 0)*c j*star (c i) := by
    have he x : H i x * F j x = Complex.exp (((((i:ℤ)+m-j):ℤ):ℂ)*Complex.I*(x:ℂ))*c j*star (c i) := by
      simp only [H,F,wave, star_mul,Complex.star_def,← Complex.exp_conj,map_mul,map_neg,map_natCast,Complex.conj_ofReal,Complex.conj_I]
      push_cast
      rw [show ((i:ℂ) + m - j)*Complex.I*(x:ℂ) = -((m:ℂ))*(x:ℂ)*(-Complex.I) + (-((i:ℂ))*(x:ℂ)*(-Complex.I)) + (-(j:ℂ)*(x:ℂ)*Complex.I) by ring]
      rw [Complex.exp_add,Complex.exp_add]; ring
    simp_rw [he,integral_mul_const]; change (∫ x in J, _) * _ * _ = _
    rw [orth]
    by_cases hh : j=i+m
    · simp [hh]
    · have hz : ((i:ℤ)+m-j)≠0 := by omega
      simp [hh,hz]
  have inner i : (∑' j, ∫ x, H i x * F j x ∂μ) = ∫ x, H i x * G x ∂μ := by
    rw [swapSum μ (fun j x => H i x * F j x) (fun j => ‖c i‖*‖c j‖) (hc.mul_left _)
      (fun j => (hH i).mul (hF j)) (fun j x => by simp [norm_mul,hhn,hn])]
    congr 1; funext x; exact tsum_mul_left
  have outer : (∑' i, ∫ x, H i x * G x ∂μ) = ∫ x, star (wave m x) * ((‖G x‖^2:ℝ):ℂ) ∂μ := by
    rw [swapSum μ (fun i x => H i x * G x) (fun i => ‖c i‖*(∑' n, ‖c n‖)) (hc.mul_right _)
      (fun i => (hH i).mul hG) (fun i x => by rw [norm_mul,hhn]; exact mul_le_mul_of_nonneg_left (hGn x) (norm_nonneg _))]
    apply integral_congr_ae; apply ae_of_all; intro x
    change (∑' n, H n x * G x) = star (wave m x) * ((‖G x‖^2:ℝ):ℂ)
    rw [tsum_mul_right]
    change (∑' n, star (wave m x) * star (F n x))*G x = _
    rw [tsum_mul_left,← tsum_star,mul_assoc,Complex.sq_norm,Complex.normSq_eq_conj_mul_self]; rfl
  change (∫ x, star (wave m x) * ((‖G x‖^2:ℝ):ℂ) ∂μ) = _
  rw [← outer]
  simp_rw [← inner, hstep]
  rw [← tsum_mul_left]
  apply tsum_congr; intro n
  rw [tsum_eq_single (n+m)]
  · simp; ring
  · intro j hj; simp [hj]
theorem solution (q α : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    let A := fun t : ℝ => ∑' n : ℕ,
      (((Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n)*q^n:ℝ):ℂ) *
        Complex.exp (Complex.I*((-((n:ℝ)*t)):ℝ))
    let p := fun x : ℝ => Real.sqrt (1-q^2)/(2*Real.pi) * ‖A (x-α)‖^2
    ∃ R : ℝ, q / 2 * (∫ x in Set.Ico 0 (2*Real.pi), p x) ≤ R ∧
      (∫ x in Set.Ico 0 (2*Real.pi), Complex.exp ((x:ℂ)*Complex.I) * (p x:ℂ)) =
        Complex.exp ((α:ℂ)*Complex.I)*(R:ℂ) := by
  let u := Complex.exp ((α:ℂ)*Complex.I)
  let v (n : ℕ) := b n*q^n
  let c (n : ℕ) := (v n:ℂ)*u^n
  let d (t : ℝ) := ‖∑' n, c n*wave n t‖^2
  let w := Real.sqrt (1-q^2)/(2*Real.pi)
  let L := ∑' n : ℕ, v n*v n
  let K := ∑' n : ℕ, v (n+1)*v n
  have vn n : 0 ≤ v n := mul_nonneg (bn n) (pow_nonneg hq n)
  have vu n : v n ≤ 1 := (mul_le_of_le_one_left (pow_nonneg hq _) (b1 _)).trans (pow_le_one₀ hq hq'.le)
  have un : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have cn n : ‖c n‖=v n := by simp [c,norm_mul,un,Real.norm_eq_abs,abs_of_nonneg (vn n)]
  have cs : Summable fun n => ‖c n‖ := by simpa only [cn] using b_sum q hq hq'
  have id (n : ℕ) (x : ℝ) : c n * wave n x =
        (v n:ℂ)*Complex.exp (Complex.I*((-((n:ℝ)*(x-α))):ℝ)) := by
    dsimp [c,wave,u]
    rw [← Complex.exp_nat_mul,mul_assoc,← Complex.exp_add]
    congr 1; push_cast; ring_nf
  have htw (n : ℕ) : u^n * star (u^n) = 1 := by
    rw [Complex.star_def, Complex.mul_conj']; simp [un]
  have hzero (n : ℕ) : c n * star (c n) = (v n*v n:ℝ) := by
    simp only [c,star_mul,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul]
    have h := htw n; rw [Complex.star_def] at h
    calc
      _ = ((v n:ℂ)*(v n:ℂ))*(u^n*conj (u^n)) := by ring
      _ = _ := by rw [h,mul_one]
  have hone (n : ℕ) : c (n+1)*star (c n) = u*(v (n+1)*v n:ℝ) := by
    simp only [c,pow_succ,star_mul,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul]
    have h := htw n; rw [Complex.star_def] at h
    calc
      _ = (u*((v (n+1):ℂ)*(v n:ℂ)))*(u^n*conj (u^n)) := by ring
      _ = _ := by rw [h,mul_one]
  have hL : (∫ x in J, d x) = P*L := by
    have h := fourier_autocorrelation c cs 0
    have e (x : ℝ) : star (wave 0 x) = 1 := by simp [wave]
    simp only [e,one_mul,Nat.add_zero,hzero] at h
    rw [integral_complex_ofReal,← Complex.ofReal_tsum,← Complex.ofReal_mul] at h
    exact Complex.ofReal_injective h
  have hK : (∫ x in J, Complex.exp ((x:ℂ)*Complex.I)* (d x:ℂ)) = (P:ℂ)*u*(K:ℂ) := by
    have h := fourier_autocorrelation c cs 1
    have he (x : ℝ) : star (wave 1 x) = Complex.exp ((x:ℂ)*Complex.I) := by
      simp only [wave,Complex.star_def,← Complex.exp_conj,map_mul,map_neg,map_natCast, Complex.conj_ofReal, Complex.conj_I]; congr 1; ring
    simp_rw [he,hone] at h
    rw [tsum_mul_left,← Complex.ofReal_tsum,← mul_assoc] at h
    exact h
  have hLsum : Summable fun n => v n*v n := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (vn _) (vn _)) (fun n => mul_le_of_le_one_left (vn _) (vu _)) (b_sum q hq hq')
  have hKsum : Summable fun n => v (n+1)*v n := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (vn _) (vn _)) (fun n => mul_le_of_le_one_left (vn _) (vu _)) (b_sum q hq hq')
  have hLK : (q/2)*L ≤ K := by
    change (q/2)*(∑' n, v n*v n) ≤ ∑' n, v (n+1)*v n
    rw [← tsum_mul_left]
    apply (hLsum.mul_left _).tsum_le_tsum _ hKsum
    intro n
    rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (vn n)
    dsimp [v]; rw [b_rec,pow_succ]
    have hr : (1/2:ℝ) ≤ Real.sqrt (((n:ℝ)+1/2)/(n+1)) := by
      apply Real.le_sqrt_of_sq_le; apply (le_div_iff₀ (by positivity)).mpr; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    nlinarith [mul_le_mul_of_nonneg_right hr (mul_nonneg (mul_nonneg hq (bn n)) (pow_nonneg hq n))]
  have hw : 0 ≤ w := div_nonneg (Real.sqrt_nonneg _) ppos.le
  refine ⟨w*P*K,?_,?_⟩
  · change (q/2)*(∫ x in J, w*‖∑' n:ℕ, (v n:ℂ)*_‖^2) ≤ _
    simp_rw [← id]; change (q/2)*(∫ x in J, w*d x) ≤ _
    rw [integral_const_mul,hL]
    nlinarith [mul_le_mul_of_nonneg_left hLK (mul_nonneg hw ppos.le)]
  · change (∫ x in J, Complex.exp ((x:ℂ)*Complex.I)*(↑(w*‖∑' n:ℕ, (v n:ℂ)*_‖^2):ℂ)) = _
    simp_rw [← id,Complex.ofReal_mul]
    change (∫ x in J, Complex.exp ((x:ℂ)*Complex.I)*((w:ℂ)*(d x:ℂ))) = _
    simp_rw [mul_left_comm (Complex.exp _) (w:ℂ)]
    rw [integral_const_mul,hK]; push_cast; ring
