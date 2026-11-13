-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.Dkernel_bound_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:42:03.688185+00:00
-- url     : https://prove2.me/submissions/1b78a5c1-683c-44ee-a9d1-d5b01aa27922

import Mathlib
import Definitions.Def_OAIQ334E004
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_boundD_mem_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Auxiliary_IntegralBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace AtomicTriangular.IntegralVectors
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma weighted_interval_bound {a b t M : ℝ} (hab : a≤b) (hbt : b≤t)
    (f : ℝ → E) (hf : ∀ x ∈ Icc a b, ‖f x‖≤M) :
    ‖∫ x in a..b, (t-x) • f x‖ ≤ ((t-a)^2-(t-b)^2)/2*M := by
  calc
    _ ≤ ∫ x in a..b, (t-x)*M := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
      · exact ae_of_all _ fun x hx => by
          rw [norm_smul,Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr (hx.2.trans hbt))]
          exact mul_le_mul_of_nonneg_left (hf x ⟨hx.1.le,hx.2⟩) (sub_nonneg.mpr (hx.2.trans hbt))
      · exact (show Continuous (fun x : ℝ => (t-x)*M) by fun_prop).intervalIntegrable a b
    _ = _ := by
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_sub (f:=fun _ : ℝ => t)
        (g:=fun x : ℝ => x) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),integral_id]
      simp only [intervalIntegral.integral_const,smul_eq_mul]
      ring

lemma norm_integral_grid {δ : ℝ} (hδ : 0≤δ) (n : ℕ) (f : ℝ → E) (hf : Continuous f)
    (M : ℕ → ℝ) (hM : ∀ i<n, ∀ x ∈ Icc ((i:ℝ)*δ) ((i+1:ℕ)*δ), ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..(n:ℝ)*δ, f x‖ ≤ δ*∑ i ∈ Finset.range n, M i := by
  have hi := intervalIntegral.sum_integral_adjacent_intervals (a:=fun i : ℕ => (i:ℝ)*δ)
    (μ:=volume) (n:=n) (f:=f) (fun i _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero,zero_mul] at hi
  rw [←hi]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖∫ x in (i:ℝ)*δ..(i+1:ℕ)*δ, f x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, δ*M i := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun x hx => hM i (Finset.mem_range.mp hi) x (by
          rw [Set.uIoc_of_le (show (i:ℝ)*δ≤(i+1:ℕ)*δ by push_cast <;> nlinarith)] at hx
          exact ⟨hx.1.le,hx.2⟩))
        (a := (i:ℝ)*δ) (b := (i+1:ℕ)*δ)
      have hd : |((i+1:ℕ):ℝ)*δ-(i:ℝ)*δ|=δ := by
        rw [show ((i+1:ℕ):ℝ)*δ-(i:ℝ)*δ=δ by push_cast; ring,abs_of_nonneg hδ]
      rw [hd] at hh
      simpa only [mul_comm] using hh
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma weighted_integral_grid {δ : ℝ} (hδ : 0≤δ) (n : ℕ) (f : ℝ → E) (hf : Continuous f)
    (M : ℕ → ℝ) (hM : ∀ i<n, ∀ x ∈ Icc ((i:ℝ)*δ) ((i+1:ℕ)*δ), ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..(n:ℝ)*δ, ((n:ℝ)*δ-x) • f x‖ ≤
      δ^2*∑ i ∈ Finset.range n, ((n:ℝ)-i-1/2)*M i := by
  have hc : Continuous (fun x : ℝ => ((n:ℝ)*δ-x) • f x) := by fun_prop
  have hi := intervalIntegral.sum_integral_adjacent_intervals (a:=fun i : ℕ => (i:ℝ)*δ)
    (μ:=volume) (n:=n) (f:=fun x : ℝ => ((n:ℝ)*δ-x) • f x) (fun i _ => hc.intervalIntegrable _ _)
  simp only [Nat.cast_zero,zero_mul] at hi
  rw [←hi]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖∫ x in (i:ℝ)*δ..(i+1:ℕ)*δ, ((n:ℝ)*δ-x) • f x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, δ^2*((n:ℝ)-i-1/2)*M i := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i+1≤n := Finset.mem_range.mp hi
      have hiR : ((i+1:ℕ):ℝ)≤n := by exact_mod_cast hin
      have hh := weighted_interval_bound (show (i:ℝ)*δ≤(i+1:ℕ)*δ by push_cast <;> nlinarith)
        (mul_le_mul_of_nonneg_right hiR hδ) f (hM i (Finset.mem_range.mp hi))
      calc
        _ ≤ (((n:ℝ)*δ-(i:ℝ)*δ)^2-((n:ℝ)*δ-((i+1:ℕ):ℝ)*δ)^2)/2*M i := by
          exact hh
        _ = _ := by push_cast <;> ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
lemma norm_integral_neg (f : ℝ → E) (t : ℝ) :
    ‖∫ x in (0:ℝ)..-t, f x‖ = ‖∫ x in (0:ℝ)..t, f (-x)‖ := by
  rw [intervalIntegral.integral_comp_neg,neg_zero,intervalIntegral.integral_symm,norm_neg]
lemma norm_weighted_integral_neg (f : ℝ → E) (t : ℝ) :
    ‖∫ x in (0:ℝ)..-t, (-t-x) • f x‖ = ‖∫ x in (0:ℝ)..t, (t-x) • f (-x)‖ := by
  rw [norm_integral_neg]
  simp only [show ∀ x : ℝ, -t- -x=-(t-x) by intro x; ring,neg_smul,
    intervalIntegral.integral_neg,norm_neg]
lemma norm_integral_grid_abs {δ t : ℝ} (hδ : 0≤δ) (n : ℕ) (ht : |t|=(n:ℝ)*δ)
    (f : ℝ → E) (hf : Continuous f) (M : ℕ → ℝ)
    (hM : ∀ i<n, ∀ x, (i:ℝ)*δ≤|x| → |x|≤(i+1:ℕ)*δ → ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..t, f x‖ ≤ δ*∑ i ∈ Finset.range n, M i := by
  rcases le_total 0 t with ht0|ht0
  · rw [abs_of_nonneg ht0] at ht
    rw [ht]
    exact norm_integral_grid hδ n f hf M (fun i hi x hx => hM i hi x
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
  · rw [abs_of_nonpos ht0] at ht
    have hte : t= -((n:ℝ)*δ) := by linarith
    rw [hte,norm_integral_neg]
    exact norm_integral_grid hδ n (fun x => f (-x)) (hf.comp continuous_neg) M (fun i hi x hx => hM i hi (-x)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
lemma weighted_integral_grid_abs {δ t : ℝ} (hδ : 0≤δ) (n : ℕ) (ht : |t|=(n:ℝ)*δ)
    (f : ℝ → E) (hf : Continuous f) (M : ℕ → ℝ)
    (hM : ∀ i<n, ∀ x, (i:ℝ)*δ≤|x| → |x|≤(i+1:ℕ)*δ → ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..t, (t-x) • f x‖ ≤ δ^2*∑ i ∈ Finset.range n, ((n:ℝ)-i-1/2)*M i := by
  rcases le_total 0 t with ht0|ht0
  · rw [abs_of_nonneg ht0] at ht
    rw [ht]
    exact weighted_integral_grid hδ n f hf M (fun i hi x hx => hM i hi x
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
  · rw [abs_of_nonpos ht0] at ht
    have hte : t= -((n:ℝ)*δ) := by linarith
    rw [hte,norm_weighted_integral_neg]
    exact weighted_integral_grid hδ n (fun x => f (-x)) (hf.comp continuous_neg) M (fun i hi x hx => hM i hi (-x)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
end AtomicTriangular.IntegralVectors
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.Envelope
open Real

lemma mul_exp_neg_le {x y δ : ℝ} (hx : 0<x) (hxy : x≤y) (hδ : 1≤δ*x) :
    y*exp (-δ*y)≤x*exp (-δ*x) := by
  have hx0 : x≠0 := ne_of_gt hx
  have hr : y/x≤δ*(y-x)+1 := by
    apply (div_le_iff₀ hx).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hδ)]
  have he : y/x≤exp (δ*(y-x)) := hr.trans (add_one_le_exp _)
  calc
    y*exp (-δ*y) = (y/x)*(x*exp (-δ*y)) := by field_simp
    _ ≤ exp (δ*(y-x))*(x*exp (-δ*y)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = x*exp (-δ*x) := by
      rw [mul_left_comm,←exp_add]
      congr 2
      ring

lemma sqrt_prefactor_identity {x a p c d δ : ℝ} (hx : 0<x) :
    (a+p*sqrt (c+d*x))*sqrt x*exp (-δ*x) =
      (a/sqrt x+p*sqrt (c/x+d))*(x*exp (-δ*x)) := by
  have hs : sqrt x≠0 := ne_of_gt (sqrt_pos.mpr hx)
  have he : c/x+d=(c+d*x)/x := by field_simp
  rw [he,sqrt_div' _ hx.le]
  have hh := sq_sqrt hx.le
  field_simp
  rw [hh]
  ring

lemma sqrt_exp_antitone {x y a p c d δ : ℝ} (hx : 0<x) (hxy : x≤y)
    (ha : 0≤a) (hp : 0≤p) (hc : 0 ≤ c) (hδ : 1≤δ*x) :
    (a+p*sqrt (c+d*y))*sqrt y*exp (-δ*y) ≤
      (a+p*sqrt (c+d*x))*sqrt x*exp (-δ*x) := by
  have hy : 0<y := hx.trans_le hxy
  rw [sqrt_prefactor_identity hy,sqrt_prefactor_identity hx]
  have hfactor : a/sqrt y+p*sqrt (c/y+d) ≤ a/sqrt x+p*sqrt (c/x+d) := by
    apply add_le_add
    · exact div_le_div_of_nonneg_left ha (sqrt_pos.mpr hx) (sqrt_le_sqrt hxy)
    · apply mul_le_mul_of_nonneg_left _ hp
      apply sqrt_le_sqrt
      simpa only [add_comm] using add_le_add_right (div_le_div_of_nonneg_left hc hx hxy) d
  exact mul_le_mul hfactor (mul_exp_neg_le hx hxy hδ) (by positivity) (by positivity)
end AtomicTriangular.Envelope
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma Xwave_pos {k : ℝ} (hk : 0<k) (t : ℝ) : 0<Xwave k t := by
  unfold Xwave
  exact div_pos (by norm_num) (waveDen_pos hk t)
lemma Xwave_square {k : ℝ} (hk : 0<k) (t : ℝ) :
    (k^2+t^2)*Xwave k t=4/3 := by
  unfold Xwave waveDen
  field_simp [ne_of_gt (waveDen_pos hk t)]
lemma normSq_lambda {k : ℝ} (hk : 0<k) (t : ℝ) : normSq (lambda k t)=Xwave k t := by
  unfold lambda
  rw [map_div₀]
  simp only [normSq_apply,add_re,ofReal_re,mul_re,I_re,zero_mul,I_im,ofReal_im,
    mul_zero,sub_zero,add_zero,add_im,mul_im,one_mul,zero_add]
  dsimp [Xwave,waveDen]
  have hb := b_sq
  have hd : k^2+t^2≠0 := ne_of_gt (waveDen_pos hk t)
  field_simp [ne_of_gt b_pos, hd]
  nlinarith [mul_nonneg (sq_nonneg k) (sq_nonneg t)]
lemma norm_lambda {k : ℝ} (hk : 0<k) (t : ℝ) : ‖lambda k t‖=Real.sqrt (Xwave k t) := by
  rw [Complex.norm_def,normSq_lambda hk]
lemma normSq_zeta {k : ℝ} (hk : 0<k) (v t : ℝ) :
    normSq (zeta k v t)=v^2+(4/3-2*k*v)*Xwave k t := by
  unfold zeta
  simp only [normSq_apply,add_re,neg_re,mul_re,ofReal_re,ofReal_im,mul_zero,
    sub_zero,I_re,zero_mul,I_im,one_mul,add_zero,add_im,neg_im,mul_im,zero_add]
  linear_combination Xwave k t * Xwave_square hk t
lemma wavePhase_re (k v t : ℝ) : (I*Real.pi*zeta k v t).re = -Real.pi*(k*Xwave k t-v) := by
  simp [zeta,mul_re,mul_im]
lemma norm_wavePhase {k : ℝ} (hk : 0<k) (v t : ℝ) :
    ‖I*Real.pi*zeta k v t‖=Real.pi*Real.sqrt (v^2+(4/3-2*k*v)*Xwave k t) := by
  rw [norm_mul,norm_mul,norm_I,one_mul,norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_def,normSq_zeta hk]

lemma Xwave_antitone {k s t : ℝ} (hk : 0<k) (hs : 0 ≤ s) (hst : s ≤ t) :
    Xwave k t≤Xwave k s := by
  unfold Xwave
  apply div_le_div_of_nonneg_left (by norm_num) (waveDen_pos hk s)
  unfold waveDen
  nlinarith
lemma damping_Xwave_lower (q : Fin 2) {t : ℝ} (ht0 : 0≤t) (ht : t≤5/6) :
    1≤Real.pi*damping q*Xwave (damping q) t := by
  have hx := Xwave_antitone (damping_pos q) ht0 ht
  have hl : 1<3*damping q*Xwave (damping q) (5/6) := by
    fin_cases q <;> (first | (simp [damping,h,H,Xwave,waveDen]; all_goals first | (norm_num [damping,h,H,Xwave,waveDen]; done) | rfl | decide) | (norm_num [damping,h,H,Xwave,waveDen]; done) | norm_num [damping,h,H,Xwave,waveDen])
  have hp := Real.pi_gt_three
  have hq := damping_pos q
  have hxpos := Xwave_pos hq t
  calc
    1 ≤ 3*damping q*Xwave (damping q) (5/6) := hl.le
    _ ≤ 3*damping q*Xwave (damping q) t := mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ Real.pi*damping q*Xwave (damping q) t := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp.le hq.le) hxpos.le

lemma jetEnvelope_monotone {q v : Fin 2} {n : ℤ} (hn : 1≤n) (hQ : 0<Q n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t≤5/6) :
    jetEnvelope (damping q) (damping v) n s ≤jetEnvelope (damping q) (damping v) n t := by
  have ht0 : 0≤t := hs.trans hst
  have hx := Xwave_pos (damping_pos q) t
  have hxy := Xwave_antitone (damping_pos q) hs hst
  have hb := damping_Xwave_lower q ht0 ht
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hδ : 1≤(Real.pi*damping q*n)*Xwave (damping q) t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (le_of_lt hx),damping_pos q,Real.pi_pos]
  have hh := Envelope.sqrt_exp_antitone (a:=1+|D n|) (p:=Real.pi)
    (c:=(damping v)^2) (d:=4/3-2*damping q*damping v) hx hxy
    (by positivity) Real.pi_pos.le (sq_nonneg _) hδ
  have he (x : ℝ) : Real.exp (-Real.pi*(damping q*x-damping v)*n) =
      Real.exp (Real.pi*damping v*n)*Real.exp (-(Real.pi*damping q*n)*x) := by
    rw [←Real.exp_add]
    congr 1
    ring
  unfold jetEnvelope
  rw [he,he]
  convert! mul_le_mul_of_nonneg_left hh (show 0 ≤ Real.exp (Real.pi*damping v*n)/Q n from
    div_nonneg (Real.exp_pos _).le hQ.le) using 1 <;> first | (with_reducible_and_instances rfl) | ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma normJetEnvelope_eq {k : ℝ} (hk : 0<k) (v : ℝ) (n : ℤ) (t : ℝ) :
    normJetEnvelope k v n t = jetEnvelope k v n t := by
  rw [normJetEnvelope,norm_wavePhase hk,norm_lambda hk]
  simp only [jetEnvelope,frequencyDecay,div_eq_mul_inv,neg_mul]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_JetEnvelopeAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex
namespace AtomicTriangular.Construction
lemma norm_transformedWave (k v t : ℝ) (n : ℤ) :
    ‖transformedWave k v t n‖ = ‖lambda k t‖ * Real.exp (-frequencyDecay k v t*n) := by
  rw [transformedWave,norm_mul,Complex.norm_exp]
  congr 2
  rw [show I*Real.pi*zeta k v t*(n:ℂ) = (I*Real.pi*zeta k v t)*(n:ℂ) by rfl,
    Complex.mul_re,Complex.intCast_re,Complex.intCast_im,mul_zero,sub_zero,wavePhase_re]
  unfold frequencyDecay
  ring
lemma jetMultiplier_pair_bound (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    (∑ d : Fin 2, ‖jetMultiplier k v n d t‖) ≤ normJetEnvelope k v n t := by
  have hqi : ‖(Q n:ℂ)⁻¹‖=(Q n)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ]
  have hb : ‖(D n:ℂ)-I*Real.pi*zeta k v t‖ ≤ |D n|+‖I*Real.pi*zeta k v t‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using norm_sub_le (D n:ℂ) (I*Real.pi*zeta k v t)
  simp only [Fin.sum_univ_two,jetMultiplier,Fin.val_zero,Fin.val_one,one_ne_zero,
    ↓reduceIte,norm_mul,norm_neg,norm_one,mul_one,hqi,norm_transformedWave]
  calc
    _ ≤ (Q n)⁻¹*(‖lambda k t‖*Real.exp (-frequencyDecay k v t*n)) +
        (Q n)⁻¹*(‖lambda k t‖*Real.exp (-frequencyDecay k v t*n))*(|D n|+‖I*Real.pi*zeta k v t‖) := by
      gcongr
    _ = _ := by unfold normJetEnvelope; ring
lemma normJetEnvelope_nonneg (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    0≤normJetEnvelope k v n t := by unfold normJetEnvelope; positivity
lemma normJetEnvelope_even (k v t : ℝ) (n : ℤ) (hk : 0<k) :
    normJetEnvelope k v n (-t)=normJetEnvelope k v n t := by
  rw [normJetEnvelope_eq hk,normJetEnvelope_eq hk]
  simp [jetEnvelope,Xwave,waveDen]
lemma normJetEnvelope_abs (k v t : ℝ) (n : ℤ) (hk : 0<k) :
    normJetEnvelope k v n |t|=normJetEnvelope k v n t := by
  rcases le_total 0 t with ht|ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht,normJetEnvelope_even k v t n hk]
lemma normJetEnvelope_monotone {q v : Fin 2} {n : ℤ} (hn : 1≤n) (hQ : 0<Q n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 5 / 6) :
    normJetEnvelope (damping q) (damping v) n s≤normJetEnvelope (damping q) (damping v) n t := by
  rw [normJetEnvelope_eq (damping_pos q),normJetEnvelope_eq (damping_pos q)]
  exact jetEnvelope_monotone hn hQ hs hst ht
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_SpectralEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma frequencyDistance_le (l : Fin 31) : frequencyDistance l≤15 := by revert l; decide +kernel
lemma frequencyDistance_eq (l : Fin 31) : |frequency l| = (frequencyDistance l:ℝ)*(1/18) := by
  fin_cases l <;> (first | (simp [frequency,frequencyDistance]; all_goals first | (norm_num [frequency,frequencyDistance]; done) | rfl | decide) | (norm_num [frequency,frequencyDistance]; done) | norm_num [frequency,frequencyDistance])
lemma range_sum_15 (N : ℕ) (hN : N≤15) (F : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, F i) = ∑ i : Fin 15, if i.val<N then F i.val else 0 := by
  rw [show (∑ i : Fin 15, if i.val<N then F i.val else 0) = ∑ i ∈ Finset.range 15, if i<N then F i else 0 by
    exact Fin.sum_univ_eq_sum_range (fun i => if i<N then F i else 0) 15,←Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_range,Finset.mem_filter]
  omega
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma spectralCVector_bound (n : ℤ) (f : ℝ → E) (hf : Continuous f) (M : Fin 15 → ℝ)
    (hM : ∀ i : Fin 15, ∀ x, (i.val:ℝ)/18≤|x| → |x|≤(i.val+1:ℕ)/18 → ‖f x‖≤M i) :
    ‖spectralCVector n f‖ ≤ ∑ i : Fin 15, M i * fullTailW i 0 := by
  let M' : ℕ → ℝ := fun i => if hi : i<15 then M ⟨i,hi⟩ else 0
  have hb (l : Fin 31) :
      ‖∫ t in (0:ℝ)..frequency l, (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t)‖ ≤
      (1/18:ℝ)^2 * ∑ i : Fin 15, if i.val<frequencyDistance l then
        ((frequencyDistance l:ℝ)-i.val-1/2)*M i else 0 := by
    have hh := IntegralVectors.weighted_integral_grid_abs (by norm_num : (0:ℝ)≤1/18)
      (frequencyDistance l) (frequencyDistance_eq l)
      (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t) (by fun_prop) M'
      (fun i hi x h1 h2 => by
        have hi15 : i<15 := lt_of_lt_of_le hi (frequencyDistance_le l)
        rw [norm_smul,norm_exp_neg_phase,one_mul]
        simpa [M',hi15] using hM ⟨i,hi15⟩ x (by convert h1 using 1; ring) (by convert h2 using 1; ring))
    rw [range_sum_15 _ (frequencyDistance_le l)] at hh
    simpa [M',Fin.is_lt] using hh
  unfold spectralCVector
  calc
    _ ≤ ∑ l : Fin 31, ‖(fourierCoeff l*exp (I*Real.pi*frequency l*n)) •
        (-(Real.pi:ℂ)^2 • ∫ t in (0:ℝ)..frequency l,
          (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t))‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 31, ‖fourierCoeff l‖ * Real.pi^2*((1/18:ℝ)^2 *
        ∑ i : Fin 15, if i.val<frequencyDistance l then ((frequencyDistance l:ℝ)-i.val-1/2)*M i else 0) := by
      apply Finset.sum_le_sum
      intro l _
      simp only [norm_smul,norm_mul,norm_exp_phase,mul_one,norm_neg,norm_pow,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb l) (show 0≤‖fourierCoeff l‖*Real.pi^2 by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [fullTailW,Fin.val_zero,↓reduceIte,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
omit [CompleteSpace E] in
lemma spectralDVector_bound (n : ℤ) (f : ℝ → E) (hf : Continuous f) (M : Fin 15 → ℝ)
    (hM : ∀ i : Fin 15, ∀ x, (i.val:ℝ)/18≤|x| → |x|≤(i.val+1:ℕ)/18 → ‖f x‖≤M i) :
    ‖spectralDVector n f‖ ≤ ∑ i : Fin 15, M i * fullTailW i 1 := by
  let M' : ℕ → ℝ := fun i => if hi : i<15 then M ⟨i,hi⟩ else 0
  have hb (l : Fin 31) :
      ‖∫ t in (0:ℝ)..frequency l, exp (-I*Real.pi*(t:ℂ)*n) • f t‖ ≤
      (1/18:ℝ) * ∑ i : Fin 15, if i.val<frequencyDistance l then M i else 0 := by
    have hh := IntegralVectors.norm_integral_grid_abs (by norm_num : (0:ℝ)≤1/18)
      (frequencyDistance l) (frequencyDistance_eq l)
      (fun t : ℝ => exp (-I*Real.pi*(t:ℂ)*n) • f t) (by fun_prop) M'
      (fun i hi x h1 h2 => by
        have hi15 : i<15 := lt_of_lt_of_le hi (frequencyDistance_le l)
        rw [norm_smul,norm_exp_neg_phase,one_mul]
        simpa [M',hi15] using hM ⟨i,hi15⟩ x (by convert h1 using 1; ring) (by convert h2 using 1; ring))
    rw [range_sum_15 _ (frequencyDistance_le l)] at hh
    simpa [M',Fin.is_lt] using hh
  unfold spectralDVector
  calc
    _ ≤ ∑ l : Fin 31, ‖(fourierCoeff l*exp (I*Real.pi*frequency l*n)) •
        ((I*Real.pi) • ∫ t in (0:ℝ)..frequency l, exp (-I*Real.pi*(t:ℂ)*n) • f t)‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 31, ‖fourierCoeff l‖ * Real.pi*((1/18:ℝ) *
        ∑ i : Fin 15, if i.val<frequencyDistance l then M i else 0) := by
      apply Finset.sum_le_sum
      intro l _
      simp only [norm_smul,norm_mul,norm_exp_phase,mul_one,norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb l) (show 0≤‖fourierCoeff l‖*Real.pi by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [fullTailW,Fin.val_one,one_ne_zero,↓reduceIte,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_TailJetVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma continuous_jetVector {k : ℝ} (hk : 0<k) (v : ℝ) (n : ℤ) :
    Continuous (jetVector k v n) := by
  exact (PiLp.continuousLinearEquiv 1 ℂ (fun _ : Fin 2 => ℂ)).symm.continuous.comp
    (continuous_pi (fun d => continuous_jetMultiplier hk v n d))
lemma jetVector_norm_bound (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    ‖jetVector k v n t‖  ≤  normJetEnvelope k v n t := by
  rw [PiLp.norm_eq_of_L1]
  exact jetMultiplier_pair_bound k v t n hQ

lemma finiteEndpoint (i : Fin 15) :
    frequency ⟨i.val+16,by omega⟩ = (i.val+1:ℕ)/18 := by
  unfold frequency
  push_cast
  ring
lemma tailJetVector_bound (q v : Fin 2) (m n : ℤ) (hm : 1 ≤ m) (hQ : 0<Q m) (c : Fin 2) :
    ‖tailJetVector (damping q) (damping v) m n c‖  ≤ 
      ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) * fullTailW i c := by
  have hh (i : Fin 15) (x : ℝ) (h1 : (i.val:ℝ)/18 ≤ |x|) (h2 : |x| ≤ (i.val+1:ℕ)/18) :
      ‖jetVector (damping q) (damping v) m x‖  ≤ 
      normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) := by
    apply (jetVector_norm_bound _ _ _ _ hQ).trans
    rw [←normJetEnvelope_abs _ _ x m (damping_pos q),finiteEndpoint]
    apply normJetEnvelope_monotone hm hQ (abs_nonneg x) h2
    have hi : ((i.val+1:ℕ):ℝ) ≤ 15 := by exact_mod_cast (show i.val+1 ≤ 15 by omega)
    linarith
  fin_cases c
  · exact spectralCVector_bound n _ (continuous_jetVector (damping_pos q) _ _) _ hh
  · exact spectralDVector_bound n _ (continuous_jetVector (damping_pos q) _ _) _ hh
lemma tailJet_pair_bound (q v : Fin 2) (m n : ℤ) (hm : 1 ≤ m) (hQ : 0<Q m) (c : Fin 2) :
    (∑ d : Fin 2, |tailJet (damping q) (damping v) m n c d|)  ≤ 
      ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) * fullTailW i c := by
  apply le_trans _ (tailJetVector_bound q v m n hm hQ c)
  rw [PiLp.norm_eq_of_L1]
  exact Finset.sum_le_sum (fun d _ => Complex.abs_re_le_norm _)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeSumsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ri_mem_lt {a : RI} {x : ℝ} (hx : a.Mem x) (p : ℤ) (q : ℕ) (hq : 0<q)
    (h : a.hi*q < p*scale) : x < p/q := by
  have hh : (a.hi:ℝ)*(q:ℝ) < p*(scale:ℝ) := by exact_mod_cast h
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply (lt_div_iff₀ hqR).mpr
  have hx' := mul_le_mul_of_nonneg_right hx.2 hqR.le
  exact (mul_lt_mul_iff_right₀ scale_pos).mp (by nlinarith)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma tailTailEnvelope_bound (c : Fin 2) : tailTailEnvelope c < (23/1000000000:ℝ) := by
  apply ri_mem_lt (boundD_mem_eu c) 23 1000000000 (by norm_num)
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_TailEnvelopeSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma frequencyDecay_pos (q v : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    0 < frequencyDecay (damping q) (damping v) t := by
  have hx := Xwave_antitone (damping_pos q) (abs_nonneg t) ht
  have he : Xwave (damping q) |t|=Xwave (damping q) t := by simp [Xwave,waveDen,sq_abs]
  rw [he] at hx
  have hb : damping v < damping q * Xwave (damping q) (5/6) := by
    fin_cases q <;> fin_cases v <;> (first | (simp [damping,h,H,Xwave,waveDen]; all_goals first | (norm_num [damping,h,H,Xwave,waveDen]; done) | rfl | decide) | (norm_num [damping,h,H,Xwave,waveDen]; done) | norm_num [damping,h,H,Xwave,waveDen])
  unfold frequencyDecay
  exact mul_pos Real.pi_pos (sub_pos.mpr (hb.trans_le (mul_le_mul_of_nonneg_left hx (damping_pos q).le)))
lemma normJetEnvelope_enumerateTail (a : Fin 15) (l : ℕ) (k v t : ℝ) :
    normJetEnvelope k v (enumerateTail (a,l)).val.val t =
      normJetEnvelope k v (tailBase a) t * (Real.exp (-frequencyDecay k v t*36))^l := by
  unfold normJetEnvelope
  rw [Q_enumerateTail,D_enumerateTail]
  change _ * Real.exp (-frequencyDecay k v t * ((tailBase a + 36*(l:ℤ):ℤ):ℝ)) = _
  rw [show -frequencyDecay k v t * ((tailBase a + 36*(l:ℤ):ℤ):ℝ) =
    -frequencyDecay k v t*(tailBase a:ℝ) + (l:ℝ)*(-frequencyDecay k v t*36) by push_cast; ring,
    Real.exp_add,Real.exp_nat_mul]
  ring
lemma summable_envelope_period (q v : Fin 2) (a : Fin 15) {t : ℝ} (ht : |t|≤5/6) :
    Summable (fun l : ℕ => normJetEnvelope (damping q) (damping v) (enumerateTail (a,l)).val.val t) := by
  simp_rw [normJetEnvelope_enumerateTail]
  apply Summable.mul_left
  apply summable_geometric_of_norm_lt_one
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
  have hh := frequencyDecay_pos q v ht
  nlinarith
lemma tsum_envelope_period (q v : Fin 2) (a : Fin 15) {t : ℝ} (ht : |t|≤5/6) :
    (∑' l : ℕ, normJetEnvelope (damping q) (damping v) (enumerateTail (a,l)).val.val t) =
    normJetEnvelope (damping q) (damping v) (tailBase a) t *
      (1-Real.exp (-frequencyDecay (damping q) (damping v) t*36))⁻¹ := by
  simp_rw [normJetEnvelope_enumerateTail]
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
  have hh := frequencyDecay_pos q v ht
  nlinarith
lemma summable_tailEnvelope (q v : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    Summable (fun n : TailNode => normJetEnvelope (damping q) (damping v) n.val.val t) := by
  apply (tailEnumeration.summable_iff).mp
  apply (summable_prod_of_nonneg (fun p => normJetEnvelope_nonneg _ _ _ _ (by
    have hh := FiniteCertificate.Q_node_bounds (enumerateTail p).val.val (enumerateTail p).val.property.2
    change 0 < Q (enumerateTail p).val.val
    linarith [hh.1]))).mpr
  exact ⟨fun a => summable_envelope_period q v a ht, (hasSum_fintype _).summable⟩
lemma tsum_tailEnvelope (q v : Fin 2) (j : Fin 31) :
    (∑' n : TailNode, normJetEnvelope (damping q) (damping v) n.val.val (frequency j)) =
    tailEnvelopeSum q v j := by
  have ht : |frequency j|≤5/6 := abs_le.mpr (frequency_mem j)
  rw [←tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr (summable_tailEnvelope q v ht)
  change Summable (fun p : Fin 15 × ℕ => normJetEnvelope (damping q) (damping v) (enumerateTail p).val.val (frequency j)) at hs
  change (∑' p : Fin 15 × ℕ, normJetEnvelope (damping q) (damping v) (enumerateTail p).val.val (frequency j)) = _
  rw [hs.tsum_prod]
  simp_rw [tsum_envelope_period q v _ ht]
  rw [tsum_fintype,←Finset.sum_mul]
  rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma Node.Qpos (n : Node) : 0<Q n.val := by
  have hh := FiniteCertificate.Q_node_bounds _ n.property.2
  linarith [hh.1]
lemma tail_tail_column_bounds (q v : Fin 2) (n : ℤ) (c : Fin 2) :
    Summable (fun p : TailNode × Fin 2 => |tailJet (damping q) (damping v) p.1.val.val n c p.2|) ∧
    (∑' p : TailNode × Fin 2, |tailJet (damping q) (damping v) p.1.val.val n c p.2|)  ≤ 
      ∑ i : Fin 15, tailEnvelopeSum q v ⟨i.val+16,by omega⟩*fullTailW i c := by
  have hs (i : Fin 15) : Summable (fun m : TailNode =>
      normJetEnvelope (damping q) (damping v) m.val.val (frequency ⟨i.val+16,by omega⟩)*fullTailW i c) :=
    (summable_tailEnvelope q v (abs_le.mpr (frequency_mem _))).mul_right _
  have hsum := summable_sum (s:=Finset.univ) (fun i _ => hs i)
  have hh := paired_summable_bound (fun m d => tailJet (damping q) (damping v) m.val.val n c d)
    (fun m : TailNode => ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m.val.val (frequency ⟨i.val+16,by omega⟩)*fullTailW i c)
    hsum (fun m => tailJet_pair_bound q v _ n (by have h := m.val.property.1; omega) m.val.Qpos c)
  refine ⟨hh.1,?_⟩
  calc
    _  ≤  _ := hh.2
    _ = _ := by
      rw [Summable.tsum_finsetSum (fun i _ => hs i)]
      simp only [tsum_mul_right,tsum_tailEnvelope]
lemma tail_tail_column_bound (n : ℤ) (c : Fin 2) :
    (∑' p : TailNode × Fin 2, |tailJet h h p.1.val.val n c p.2|) < 23/10^9 := by
  exact (tail_tail_column_bounds 0 0 n c).2.trans_lt (by norm_num [tailTailEnvelope,damping,H,h] at ⊢; simpa [tailTailEnvelope] using FiniteCertificate.tailTailEnvelope_bound c)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
lemma Dkernel_bound_eu_oai (q : TailNode × Fin 2) : (∑' p, |Dkernel p q|) ≤ 23/10^9 :=
  (tail_tail_column_bound q.1.val.val q.2).le
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.Dkernel_bound_eu_oai := @OAI.AtomicTriangular.Construction.Dkernel_bound_eu_oai
