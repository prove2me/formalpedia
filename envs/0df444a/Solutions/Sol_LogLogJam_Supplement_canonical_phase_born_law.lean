-- Prove2me | solution 1 for LogLogJam.Supplement.canonical_phase_born_law
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:21:10.872911+00:00
-- url     : https://prove2.me/submissions/8c516f09-9cec-4b96-bd19-7fcb93179ee9

import Theorems.Thm_LogLogJam_Supplement_squeezed_fock_realization
import Theorems.Thm_BosonicLearn_state_ext_characteristic
open MeasureTheory BosonicLearn LogLogJam LogLogJam.Supplement Complex Filter
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Topology ComplexConjugate
set_option maxHeartbeats 850000
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

private theorem ampIntegral (c : ℕ → ℂ) (hc : Summable fun n => ‖c n‖)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∑' i : ℕ, ∑' j : ℕ, (∫ x : ℝ, Complex.exp (Complex.I*(((i:ℝ)-j)*x)) ∂μ) * c j * star (c i)) =
      ∫ x, (‖∑' n, c n * wave n x‖^2 : ℝ) ∂μ := by
  let F := fun i x => c i * wave i x
  have hn i x : ‖F i x‖ = ‖c i‖ := by simp [F,norm_mul,wave_norm]
  have hF i : Continuous (F i) := continuous_const.mul (wave_cont _)
  have hFs x : Summable (fun i => F i x) := hc.of_norm_bounded fun i => (hn i x).le
  let G := fun x => ∑' i, F i x
  have hGs : Continuous G := continuous_tsum hF hc fun i x => (hn i x).le
  have hGn x : ‖G x‖ ≤ ∑' i, ‖c i‖ := by
    calc
      _ ≤ ∑' i, ‖F i x‖ := norm_tsum_le_tsum_norm (by simpa only [hn] using hc)
      _ = _ := tsum_congr fun i => hn i x
  have hstep (i j : ℕ) : (∫ x : ℝ, Complex.exp (Complex.I*(((i:ℝ)-j)*x)) ∂μ) * c j * star (c i) =
      ∫ x, star (F i x) * F j x ∂μ := by
    rw [← integral_mul_const, ← integral_mul_const]
    apply integral_congr_ae; apply ae_of_all; intro x
    simp only [F, star_mul,← wave_pair]; ring
  have inner i : (∑' j, ∫ x, star (F i x) * F j x ∂μ) = ∫ x, star (F i x) * G x ∂μ := by
    rw [swapSum μ (fun j x => star (F i x) * F j x) (fun j => ‖c i‖ * ‖c j‖) (hc.mul_left _) (fun j => (hF i).star.mul (hF j))
      (fun j x => by simp [norm_mul, hn])]
    congr 1; funext x; exact tsum_mul_left
  simp_rw [hstep,inner]
  rw [swapSum μ (fun i x => star (F i x) * G x) (fun i => ‖c i‖*(∑' j,‖c j‖)) (hc.mul_right _) (fun i => (hF i).star.mul hGs)
    (fun i x => by rw [norm_mul,norm_star,hn]; exact mul_le_mul_of_nonneg_left (hGn x) (norm_nonneg _))]
  rw [← integral_complex_ofReal (μ:=μ) (f:=fun x => ‖∑' n, c n * wave n x‖^2)]
  apply integral_congr_ae; apply ae_of_all; intro x
  change (∑' n, star (F n x) * G x) = _
  rw [tsum_mul_right, ← tsum_star]
  change star (G x) * (G x) = ((‖G x‖^2:ℝ):ℂ)
  rw [Complex.sq_norm]; exact Complex.normSq_eq_conj_mul_self.symm
private noncomputable def bk (n : ℕ) : ℝ := Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n
private noncomputable def coeff (r θ : ℝ) (n : ℕ) : ℂ :=
  (bk n / Real.sqrt (Real.cosh r) : ℝ) * (((Real.tanh r : ℝ):ℂ)*Complex.exp ((2*θ:ℝ)*Complex.I))^n

private theorem bk_nonneg n : 0 ≤ bk n := by dsimp [bk]; positivity
private theorem bk_le_one n : bk n ≤ 1 := by
  have h : (Nat.centralBinom n:ℝ) ≤ (4:ℝ)^n := by exact_mod_cast Nat.centralBinom_le_four_pow n
  have e : (4:ℝ)^n = ((2:ℝ)^n)^2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  dsimp [bk]; rw [div_le_one (by positivity)]
  exact (Real.sqrt_le_iff.mpr ⟨by positivity,h.trans_eq e⟩)
private theorem coeff_summable (r θ : ℝ) (hr : 0 ≤ r) : Summable fun n => ‖coeff r θ n‖ := by
  have hq : 0 ≤ Real.tanh r := by rw [Real.tanh_eq_sinh_div_cosh]; exact div_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos _).le
  have hc : 0 < Real.sqrt (Real.cosh r) := Real.sqrt_pos.mpr (Real.cosh_pos _)
  have hq' := summable_geometric_of_lt_one hq (Real.tanh_lt_one r)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hq'.mul_left (1 / Real.sqrt (Real.cosh r)))
  intro n
  simp only [coeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg hq,
    abs_of_nonneg (div_nonneg (bk_nonneg _) hc.le), Complex.norm_exp_ofReal_mul_I,mul_one]
  gcongr; exact bk_le_one _

private theorem uniqState {ρ σ : State (Occupation (Fin 1))} {r θ : ℝ}
    (hρ : squeezedAt ρ r θ) (hσ : squeezedAt σ r θ) : ρ=σ := by
  have h := state_ext_characteristic ρ σ (fun ξ => (hρ.2.2 ξ).trans (hσ.2.2 ξ).symm)
  cases ρ; cases σ; congr

theorem solution (M : FockPOVM (Occupation (Fin 1)) ℝ)
    (hM : ∀ (B : Set ℝ), MeasurableSet B → ∀ i j : ℕ,
      M.effect B (fun _ => 2*i) (fun _ => 2*j) =
        (∫ x in B ∩ Set.Ico 0 (2*Real.pi), Complex.exp (Complex.I*(((i:ℝ)-j)*x))) / (2*Real.pi:ℝ))
    (ρ : State (Occupation (Fin 1))) (r θ : ℝ) (hρ : squeezedAt ρ r θ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let b := fun n : ℕ => Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n
    let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ:ℝ)*Complex.I)
    M.law ρ.coefficients B = ENNReal.ofReal ((∫ x in B ∩ Set.Ico 0 (2*Real.pi),
      ‖∑' n, (((b n / Real.sqrt (Real.cosh r) : ℝ) : ℂ) * z^n) * Complex.exp (-(n:ℂ)*(x:ℂ)*Complex.I)‖^2) / (2 * Real.pi)) := by
  classical
  let z := (Real.tanh r:ℂ) * Complex.exp ((2*θ:ℝ)*Complex.I)
  let c := coeff r θ
  let w := fun n : ℕ => if Even n then c (n/2) else 0
  obtain ⟨σ,hσ,hs⟩ := squeezed_fock_realization r θ hρ.1
  have hcoeff (u v : Occupation (Fin 1)) : ρ.coefficients u v = w (u 0) * star (w (v 0)) := by
    rw [uniqState hρ hσ,hs]
    congr 1
    · dsimp [w,c,coeff,bk]; split_ifs <;> simp [div_div]
    · congr 1; dsimp [w,c,coeff,bk]; split_ifs <;> simp [div_div]
  let ix (n : ℕ) : Occupation (Fin 1) := fun _ => 2*n
  have hin : Function.Injective ix := by
    intro i j e
    have h := congrFun e 0
    change 2*i=2*j at h; omega
  have hzero (i : Occupation (Fin 1)) (hi : i ∉ Set.range ix) : w (i 0) = 0 := by
    have he : ¬Even (i 0) := by
      rintro ⟨a,ha⟩
      apply hi; refine ⟨a,?_⟩; funext j; fin_cases j; change 2*a=i 0; omega
    simp [w,he]
  let f := fun (i j : Occupation (Fin 1)) => M.effect B i j * ρ.coefficients j i
  have hoff i (h : i ∉ Set.range ix) : (∑' j, f i j) = 0 := by
    simp [f,hcoeff,hzero i h]
  have hjoff i j (h : j ∉ Set.range ix) : f i j = 0 := by simp [f,hcoeff,hzero j h]
  have hred : (∑' i, ∑' j, f i j) = ∑' i, ∑' j, f (ix i) (ix j) := by
    rw [← hin.tsum_eq (f:=fun i => ∑' j, f i j) (by intro i hi; by_contra h; exact hi (hoff i h))]
    apply tsum_congr; intro i
    exact (hin.tsum_eq (f:=f (ix i)) (by intro j hj; by_contra h; exact hj (hjoff _ j h))).symm
  let μ := volume.restrict (B ∩ Set.Ico 0 (2*Real.pi))
  haveI : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ]; exact lt_of_le_of_lt (measure_mono Set.inter_subset_right)
      (measure_Ico_lt_top (a:=0) (b:=2*Real.pi))⟩
  have hw i : w (ix i 0) = c i := by simp [w,ix]
  let divi := (2*Real.pi:ℝ)
  have ht i j : f (ix i) (ix j) =
        ((∫ x, Complex.exp (Complex.I*(((i:ℝ)-j)*x)) ∂μ) * c j * star (c i)) / divi := by
    change M.effect B (ix i) (ix j) * ρ.coefficients (ix j) (ix i) = _
    rw [hcoeff,hw,hw,hM B hB i j]; dsimp [μ,divi]; ring
  rw [M.law_born _ ρ.density B hB]
  change ENNReal.ofReal (∑' i, ∑' j, f i j).re = ENNReal.ofReal _
  rw [hred]; simp_rw [ht,tsum_div_const]
  rw [ampIntegral c (coeff_summable r θ hρ.1) μ]
  rw [← Complex.ofReal_div, Complex.ofReal_re]; rfl
