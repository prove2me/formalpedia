-- Prove2me | solution 1 for LindelofHypothesis.moment_bound_of_k_le_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T01:52:20.657674+00:00
-- url     : https://prove2.me/submissions/c138472c-a451-4ae4-8c22-34843f27a204

import Mathlib
import Theorems.Thm_RSSeam_rs_Z_C0_seam
import Theorems.Thm_ArtinPrimitiveRoots_dirichlet_mean_value

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM
noncomputable section
/-!
# Fourth moment of ζ on the critical line, T^ε form: blueprint

Target: `moment_bound_of_k_le_two`, with exactly the type of `LindelofHypothesis.moment_bound_of_k_le_two`.

Route.
* (RS) `rs_pointwise`: from the Riemann–Siegel formula `RSSeam.rs_Z_C0_seam` (t ≥ 509),
  ‖ζ(1/2+it)‖ ≤ 2‖S_{N(t)}(t)‖ + 3, N(t) = ⌊√(t/2π)⌋, S_N(t) = Σ_{n≤N} n^{-1/2-it};
  valid off the countable set `bad_countable`.  Uses `psi_bound` (|Ψ| ≤ 2) and that
  Λ(1/2+it) is real.
* (F) `fourier_split`: the t-dependent cut n ≤ N(t) is removed by finite Fourier analysis
  mod M > L: ‖S_N(t)‖ ≤ Σ_{h<M} w_h ‖A_h(t)‖ with A_h(t) = Σ_{n≤L} e(hn/M) n^{-1/2-it};
  `weight_sum`: Σ_h w_h ≤ 2 + log(L+1).
* (M) `fourth_moment_poly`: ∫_{T₁}^{T₂} ‖Σ_{n≤L} a_n n^{-it}‖⁴ ≤ (T₂−T₁ + 4L²(1+log L²))(1+log L)⁴
  for |a_n| ≤ n^{-1/2}, by squaring and `ArtinPrimitiveRoots.dirichlet_mean_value`.
* (H) `power_mean`: (Σ w a)⁴ ≤ (Σ w)³ Σ w a⁴.
* (D) in Part D: ∫_T^{2T} ‖ζ‖⁴ ≤ C T (1 + log T)⁹, then ∫_0^T ‖ζ‖⁴ ≤ C T (1+log T)⁹ dyadically.
-/
/-- S_N(t) = Σ_{n=1}^{N} n^{-(1/2+it)}. -/
def S (N : ℕ) (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))

/-- The general Dirichlet polynomial Σ_{n=1}^{L} a_n n^{-it}. -/
def DP (a : ℕ → ℂ) (L : ℕ) (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 L, a n * (n : ℂ) ^ (-((t : ℂ) * I))

/-- The twisted coefficients e(hn/M) n^{-1/2}. -/
def tw (M h : ℕ) (n : ℕ) : ℂ := cexp (2 * π * I * ((h * n : ℕ) : ℂ) / M) * (n : ℂ) ^ (-(1 / 2 : ℂ))

/-- A_h(t) = Σ_{n=1}^{L} e(hn/M) n^{-(1/2+it)}. -/
def A (M L h : ℕ) (t : ℝ) : ℂ := DP (tw M h) L t

/-- The Fourier weights: w_0 = L/M, w_h = 1/(M sin(π h / M)) for 0 < h. -/
def w (M L h : ℕ) : ℝ :=
  if h = 0 then (L : ℝ) / M else 1 / ((M : ℝ) * Real.sin (π * h / M))

end
end GuthMaynard.CitedZeros.FM
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real ComplexConjugate
namespace GuthMaynard.CitedZeros.FM.PartR
open GuthMaynard.CitedZeros.FM
noncomputable section
lemma abs_sin_ge {x : ℝ} (hx : |x| ≤ π / 2) : 2 / π * |x| ≤ |Real.sin x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx ⊢
    have := Real.mul_le_sin h hx
    exact this.trans (le_abs_self _)
  · rw [abs_of_nonpos h] at hx ⊢
    have := Real.mul_le_sin (neg_nonneg.2 h) hx
    rw [Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

lemma num_eq (p : ℝ) : Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) =
    Real.sin (2 * π * ((p - 1 / 4) * (p - 3 / 4))) := by
  rw [← Real.cos_sub_pi_div_two]
  congr 1; ring

theorem psi_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (hc : Real.cos (2 * π * p) ≠ 0) :
    |RSInt.rsPsi p| ≤ 2 := by
  unfold RSInt.rsPsi
  rw [abs_div, div_le_iff₀ (abs_pos.2 hc), num_eq]
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_four
  have hnum : |Real.sin (2 * π * ((p - 1 / 4) * (p - 3 / 4)))| ≤
      2 * π * (|p - 1 / 4| * |p - 3 / 4|) := by
    refine (Real.abs_sin_le_abs).trans ?_
    simp only [abs_mul, abs_two, abs_of_pos hpi, le_refl]
  rcases le_total p (1 / 2) with h | h
  · have hc' : Real.cos (2 * π * p) = Real.sin (2 * π * (1 / 4 - p)) := by
      rw [← Real.cos_pi_div_two_sub]; congr 1; ring
    have hx : |2 * π * (1 / 4 - p)| ≤ π / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    have hs := abs_sin_ge hx
    rw [← hc'] at hs
    have e : |2 * π * (1 / 4 - p)| = 2 * π * |p - 1 / 4| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π), abs_sub_comm]
    rw [e] at hs
    have h34 : |p - 3 / 4| ≤ 3 / 4 := by rw [abs_le]; constructor <;> linarith
    have ha := abs_nonneg (p - 1 / 4)
    have : 2 / π * (2 * π * |p - 1 / 4|) = 4 * |p - 1 / 4| := by field_simp; ring
    rw [this] at hs
    calc _ ≤ 2 * π * (|p - 1 / 4| * |p - 3 / 4|) := hnum
      _ ≤ 2 * π * (|p - 1 / 4| * (3 / 4)) := by gcongr
      _ ≤ 2 * (4 * |p - 1 / 4|) := by nlinarith
      _ ≤ _ := by linarith
  · have hc' : Real.cos (2 * π * p) = Real.sin (2 * π * (p - 3 / 4)) := by
      rw [← Real.cos_sub_pi_div_two]
      have : 2 * π * (p - 3 / 4) - π / 2 = 2 * π * p - 2 * π := by ring
      rw [this, Real.cos_sub_two_pi]
    have hx : |2 * π * (p - 3 / 4)| ≤ π / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    have hs := abs_sin_ge hx
    rw [← hc'] at hs
    have e : |2 * π * (p - 3 / 4)| = 2 * π * |p - 3 / 4| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    rw [e] at hs
    have h14 : |p - 1 / 4| ≤ 3 / 4 := by rw [abs_le]; constructor <;> linarith
    have ha := abs_nonneg (p - 3 / 4)
    have : 2 / π * (2 * π * |p - 3 / 4|) = 4 * |p - 3 / 4| := by field_simp; ring
    rw [this] at hs
    calc _ ≤ 2 * π * (|p - 1 / 4| * |p - 3 / 4|) := hnum
      _ ≤ 2 * π * ((3 / 4) * |p - 3 / 4|) := by gcongr
      _ ≤ 2 * (4 * |p - 3 / 4|) := by nlinarith
      _ ≤ _ := by linarith

end
end GuthMaynard.CitedZeros.FM.PartR
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM
noncomputable section
/-! ## (RS) -/

end
end GuthMaynard.CitedZeros.FM
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real ComplexConjugate
namespace GuthMaynard.CitedZeros.FM.PartR
open GuthMaynard.CitedZeros.FM
noncomputable section
lemma rsFrac_nonneg (t : ℝ) : 0 ≤ RSInt.rsFrac t := by
  unfold RSInt.rsFrac RSInt.rsNn RSInt.rsAlpha
  linarith [Nat.floor_le (Real.sqrt_nonneg (t / (2 * π)))]

lemma rsFrac_lt_one (t : ℝ) : RSInt.rsFrac t < 1 := by
  unfold RSInt.rsFrac RSInt.rsNn
  linarith [Nat.lt_floor_add_one (RSInt.rsAlpha t)]

lemma GammaR_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj]
  have h1 : -conj s / 2 = conj (-s / 2) := by simp [map_div₀, map_ofNat]
  have h2 : conj s / 2 = conj (s / 2) := by simp [map_div₀, map_ofNat]
  rw [h1, h2, Complex.cpow_conj _ _ (by simp [Complex.arg_ofReal_of_nonneg Real.pi_pos.le,
    Real.pi_ne_zero.symm])]
  simp

lemma completed_conj (s : ℂ) (h0 : s ≠ 0) (hre : 0 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hc0 : conj s ≠ 0 := by simpa using h0
  have hre' : 0 < (conj s).re := by simpa using hre
  have e1 := riemannZeta_def_of_ne_zero h0
  have e2 := riemannZeta_def_of_ne_zero hc0
  have g1 := Gammaℝ_ne_zero_of_re_pos hre
  have g2 := Gammaℝ_ne_zero_of_re_pos hre'
  rw [eq_div_iff g1] at e1
  rw [eq_div_iff g2] at e2
  rw [← e1, ← e2, riemannZeta_conj, GammaR_conj, map_mul]

lemma completed_im_zero (t : ℝ) : (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).im = 0 := by
  set s : ℂ := (1 / 2 : ℂ) + t * I
  have h0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [s] at this
  have hre : 0 < s.re := by simp [s]
  have hcs : conj s = 1 - s := by
    apply Complex.ext <;> simp [s]; norm_num
  have := completed_conj s h0 hre
  rw [hcs, completedRiemannZeta_one_sub] at this
  exact Complex.conj_eq_iff_im.1 this.symm

lemma term_re (φ t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (cexp (I * φ) * (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))).re =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Complex.cpow_def_of_ne_zero hc, ← Complex.exp_add]
  have hl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn0.le]
  rw [hl, Complex.exp_re, Real.rpow_def_of_pos hn0]
  generalize Real.log (n : ℝ) = L
  congr 1
  · congr 1; simp
  · congr 1; simp; ring

theorem rs_pointwise (t : ℝ) (ht : 509 ≤ t) (hp : 0 < RSInt.rsFrac t)
    (hcos : Real.cos (2 * π * RSInt.rsFrac t) ≠ 0) :
    ‖riemannZeta (1 / 2 + t * I)‖ ≤ 2 * ‖S (RSInt.rsNn t) t‖ + 3 := by
  obtain ⟨M, φ, hM, hG, -, hb⟩ := RSSeam.rs_Z_C0_seam ht hp hcos
  set s : ℂ := (1 / 2 : ℂ) + t * I with hs
  have h0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [s] at this
  have enorm1 : ‖cexp (I * φ)‖ = 1 := by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hz : ‖riemannZeta s‖ = |(completedRiemannZeta s).re / M| := by
    rw [riemannZeta_def_of_ne_zero h0, norm_div, hG, norm_mul, enorm1,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, abs_div, abs_of_pos hM]
    congr 1
    have := completed_im_zero t
    rw [← hs] at this
    conv_lhs => rw [← Complex.re_add_im (completedRiemannZeta s), this]
    simp
  have hsum : ∑ n ∈ Finset.Icc 1 (RSInt.rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) *
      Real.cos (φ - t * Real.log n) = (cexp (I * φ) * S (RSInt.rsNn t) t).re := by
    rw [S, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [term_re φ t n (Finset.mem_Icc.1 hn).1]
  have hsumb : |(cexp (I * φ) * S (RSInt.rsNn t) t).re| ≤ ‖S (RSInt.rsNn t) t‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, enorm1, one_mul]
  have hpsi := psi_bound _ (rsFrac_nonneg t) (rsFrac_lt_one t) hcos
  have hpos : (0 : ℝ) < t := by linarith
  have h1 : (t / (2 * π)) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos _ (by norm_num)
    rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four]
  have h1' : 0 ≤ (t / (2 * π)) ^ (-(1 / 4 : ℝ)) := by positivity
  have h2 : 13 / 5 * t ^ (-(3 / 4 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hpos.le]
    have hq : Real.sqrt t ≤ t ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have : (22 : ℝ) ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by linarith)
    have hpos' : 0 < t ^ (3 / 4 : ℝ) := by positivity
    rw [← div_eq_mul_inv, div_le_one hpos']; linarith
  have hsign : |(-1 : ℝ) ^ (RSInt.rsNn t + 1)| = 1 := by simp
  have hterm : |(-1 : ℝ) ^ (RSInt.rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) *
      RSInt.rsPsi (RSInt.rsFrac t)| ≤ 2 := by
    rw [abs_mul, abs_mul, hsign, one_mul, abs_of_nonneg h1']
    nlinarith [abs_nonneg (RSInt.rsPsi (RSInt.rsFrac t))]
  rw [hz]
  rw [hsum] at hb
  have := abs_sub_abs_le_abs_sub ((completedRiemannZeta s).re / M)
    (2 * (cexp (I * φ) * S (RSInt.rsNn t) t).re + (-1 : ℝ) ^ (RSInt.rsNn t + 1) *
      (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * RSInt.rsPsi (RSInt.rsFrac t))
  have h3 := abs_add_le (2 * (cexp (I * φ) * S (RSInt.rsNn t) t).re) ((-1 : ℝ) ^ (RSInt.rsNn t + 1) *
      (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * RSInt.rsPsi (RSInt.rsFrac t))
  rw [abs_mul, abs_two] at h3
  linarith

end
end GuthMaynard.CitedZeros.FM.PartR
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM
noncomputable section
alias rs_pointwise := GuthMaynard.CitedZeros.FM.PartR.rs_pointwise

end
end GuthMaynard.CitedZeros.FM
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real ComplexConjugate
namespace GuthMaynard.CitedZeros.FM.PartR
open GuthMaynard.CitedZeros.FM
noncomputable section
theorem bad_countable :
    (Set.Ici (509 : ℝ) ∩ {t : ℝ | ¬ (0 < RSInt.rsFrac t ∧ Real.cos (2 * π * RSInt.rsFrac t) ≠ 0)}).Countable := by
  have hc : (Set.range (fun N : ℕ => 2 * π * (N : ℝ) ^ 2) ∪
      Set.range (fun q : ℕ × ℤ => 2 * π * ((q.1 : ℝ) + (2 * q.2 + 1) / 4) ^ 2)).Countable :=
    (Set.countable_range _).union (Set.countable_range _)
  refine hc.mono ?_
  rintro t ⟨ht, hbad⟩
  simp only [Set.mem_Ici] at ht
  simp only [Set.mem_ofPred_eq, not_and_or, not_lt, not_not] at hbad
  have ht0 : 0 ≤ t / (2 * π) := by positivity
  have hα : t = 2 * π * ((RSInt.rsNn t : ℝ) + RSInt.rsFrac t) ^ 2 := by
    have : (RSInt.rsNn t : ℝ) + RSInt.rsFrac t = RSInt.rsAlpha t := by
      unfold RSInt.rsFrac; ring
    rw [this, RSInt.rsAlpha, Real.sq_sqrt ht0]
    field_simp
  rcases hbad with h | h
  · left
    have : RSInt.rsFrac t = 0 := le_antisymm h (rsFrac_nonneg t)
    refine ⟨RSInt.rsNn t, ?_⟩
    simp only
    rw [this, add_zero] at hα; exact hα.symm
  · right
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1 h
    have hp : RSInt.rsFrac t = (2 * k + 1) / 4 := by
      have hpi := Real.pi_pos
      field_simp at hk ⊢
      nlinarith
    refine ⟨(RSInt.rsNn t, k), ?_⟩
    simp only
    rw [hp] at hα; exact hα.symm

end
end GuthMaynard.CitedZeros.FM.PartR
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM
noncomputable section
alias bad_countable := GuthMaynard.CitedZeros.FM.PartR.bad_countable

end
end GuthMaynard.CitedZeros.FM
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM.PartF
open GuthMaynard.CitedZeros.FM
noncomputable section
/-! ## w_nonneg -/
theorem w_nonneg (M L h : ℕ) (hh : h < M) : 0 ≤ w M L h := by
  unfold w
  split_ifs with h0
  · positivity
  · have hM : (0 : ℝ) < M := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le h) hh)
    have hh0 : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hhM : (h : ℝ) < M := by exact_mod_cast hh
    have hs : 0 < Real.sin (π * h / M) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · rw [div_lt_iff₀ hM]; nlinarith [Real.pi_pos]
    positivity

end
end GuthMaynard.CitedZeros.FM.PartF
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM
noncomputable section
alias w_nonneg := GuthMaynard.CitedZeros.FM.PartF.w_nonneg

end
end GuthMaynard.CitedZeros.FM
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM.PartF
open GuthMaynard.CitedZeros.FM
noncomputable section
/-! ## weight_sum -/
lemma jordan (M k : ℝ) (hM : 0 < M) (hk : 0 < k) (hkM : 2 * k ≤ M) :
    2 * k / M ≤ Real.sin (π * k / M) := by
  have h1 := Real.mul_le_sin (x := π * k / M) (by positivity)
    (by rw [div_le_iff₀ hM]; nlinarith [Real.pi_pos])
  have : 2 / π * (π * k / M) = 2 * k / M := by field_simp
  linarith

lemma wk_le (M k : ℝ) (hk : 0 < k) (hkM : k < M) :
    1 / (M * Real.sin (π * k / M)) ≤ 1 / (2 * k) + 1 / (2 * (M - k)) := by
  have hM : 0 < M := by linarith
  rcases le_or_gt (2 * k) M with h | h
  · have hs := jordan M k hM hk h
    have : 2 * k ≤ M * Real.sin (π * k / M) := by
      rw [div_le_iff₀ hM] at hs; linarith
    have h2 : 1 / (M * Real.sin (π * k / M)) ≤ 1 / (2 * k) :=
      one_div_le_one_div_of_le (by positivity) this
    have : 0 ≤ 1 / (2 * (M - k)) := by
      have : 0 < M - k := by linarith
      positivity
    linarith
  · have hs := jordan M (M - k) hM (by linarith) (by linarith)
    have he : Real.sin (π * (M - k) / M) = Real.sin (π * k / M) := by
      rw [show π * (M - k) / M = π - π * k / M by field_simp, Real.sin_pi_sub]
    rw [he] at hs
    have : 2 * (M - k) ≤ M * Real.sin (π * k / M) := by
      rw [div_le_iff₀ hM] at hs; linarith
    have h2 : 1 / (M * Real.sin (π * k / M)) ≤ 1 / (2 * (M - k)) :=
      one_div_le_one_div_of_le (by nlinarith) this
    have : 0 ≤ 1 / (2 * k) := by positivity
    linarith

theorem weight_sum (L : ℕ) (hL : 1 ≤ L) :
    ∑ h ∈ Finset.range (L + 1), w (L + 1) L h ≤ 2 + Real.log (L + 1) := by
  rw [Finset.sum_range_succ']
  have h0 : w (L + 1) L 0 ≤ 1 := by
    unfold w; simp only [if_true]
    rw [div_le_one (by positivity)]; push_cast; linarith
  have hk : ∀ j ∈ Finset.range L, w (L + 1) L (j + 1) ≤
      1 / (2 * ((j : ℝ) + 1)) + 1 / (2 * ((L : ℝ) - j)) := by
    intro j hj
    have hj' : j < L := Finset.mem_range.mp hj
    unfold w
    simp only [Nat.add_one_ne_zero, if_false]
    have := wk_le ((L + 1 : ℕ) : ℝ) ((j + 1 : ℕ) : ℝ) (by positivity)
      (by exact_mod_cast (by omega : j + 1 < L + 1))
    push_cast at this ⊢
    convert this using 3
    ring
  have hsum := Finset.sum_le_sum hk
  rw [Finset.sum_add_distrib] at hsum
  have hrefl : ∑ j ∈ Finset.range L, 1 / (2 * ((L : ℝ) - j)) =
      ∑ j ∈ Finset.range L, 1 / (2 * ((j : ℝ) + 1)) := by
    rw [← Finset.sum_range_reflect (fun j : ℕ => 1 / (2 * ((j : ℝ) + 1))) L]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < L := Finset.mem_range.mp hj
    have : ((L - 1 - j : ℕ) : ℝ) = (L : ℝ) - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [this]; ring_nf
  have hH : ∑ j ∈ Finset.range L, 1 / (2 * ((j : ℝ) + 1)) = (harmonic L : ℝ) / 2 := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    field_simp
  have hlog := harmonic_le_one_add_log L
  have hmono : Real.log L ≤ Real.log (L + 1) :=
    Real.log_le_log (by exact_mod_cast hL) (by linarith)
  rw [hrefl, hH] at hsum
  linarith

/-! ## fourier_split -/
lemma tw_eq (M h n : ℕ) :
    tw M h n = (cexp (2 * π * I / M)) ^ (h * n) * (n : ℂ) ^ (-(1 / 2 : ℂ)) := by
  unfold tw
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma cpow_split (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) = (n : ℂ) ^ (-(1 / 2 : ℂ)) * (n : ℂ) ^ (-((t : ℂ) * I)) := by
  rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast hn)]

lemma orth (M : ℕ) (hM : 0 < M) (n m : ℕ) (hn : n < M) (hm : m < M) :
    ∑ h ∈ Finset.range M, ((cexp (2 * π * I / M)) ^ m)⁻¹ ^ h * (cexp (2 * π * I / M)) ^ (h * n)
      = if n = m then (M : ℂ) else 0 := by
  set ζ := cexp (2 * π * I / M) with hζdef
  have hζ : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hM.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hterm : ∀ h, (ζ ^ m)⁻¹ ^ h * ζ ^ (h * n) = (ζ ^ n * (ζ ^ m)⁻¹) ^ h := by
    intro h
    rw [mul_pow, ← pow_mul, mul_comm n h, mul_comm]
  simp_rw [hterm]
  split_ifs with hnm
  · subst hnm
    rw [mul_inv_cancel₀ (pow_ne_zero _ hζ0)]
    simp
  · have hx1 : ζ ^ n * (ζ ^ m)⁻¹ ≠ 1 := by
      intro h
      have : ζ ^ n = ζ ^ m := by
        have := congrArg (· * ζ ^ m) h
        simpa [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hζ0)] using this
      exact hnm (hζ.pow_inj hn hm this)
    rw [geom_sum_eq hx1]
    have : (ζ ^ n * (ζ ^ m)⁻¹) ^ M = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm n, mul_comm m, pow_mul, pow_mul,
        hζ.pow_eq_one]
      simp
    rw [this]; simp

lemma D_bound (M L N h : ℕ) (hLM : L < M) (hNL : N ≤ L) (hh : h < M) :
    ‖(1 / (M : ℂ)) * ∑ m ∈ Finset.Icc 1 N, ((cexp (2 * π * I / M)) ^ m)⁻¹ ^ h‖ ≤ w M L h := by
  set ζ := cexp (2 * π * I / M) with hζdef
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hLM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hζ : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hM.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hM.ne'
  unfold w
  split_ifs with h0
  · subst h0
    simp only [pow_zero, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast, Complex.norm_natCast]
    simp only [add_tsub_cancel_right]
    rw [one_div_mul_eq_div]
    gcongr
  · have hhpos : 0 < h := Nat.pos_of_ne_zero h0
    set z := (ζ ^ h)⁻¹ with hz
    have hzm : ∀ m, (ζ ^ m)⁻¹ ^ h = z ^ m := by
      intro m; rw [hz, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
    simp_rw [hzm]
    have hzh1 : ζ ^ h ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hhpos.ne' hh
    have hz1 : z ≠ 1 := by
      rw [hz]; intro e; exact hzh1 (inv_eq_one.mp e)
    have hzn : ‖z‖ = 1 := by rw [hz, norm_inv, norm_pow, hζn]; simp
    have hsum : ∑ m ∈ Finset.Icc 1 N, z ^ m = z * ((z ^ N - 1) / (z - 1)) := by
      rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext; simp, Finset.sum_Ico_eq_sum_range, ← geom_sum_eq hz1, Finset.mul_sum]
      apply Finset.sum_congr (by simp) ; intro k _; ring
    -- ‖z - 1‖ = 2 sin(π h / M)
    have hs : 0 < Real.sin (π * h / M) := by
      have hhM : (h : ℝ) < M := by exact_mod_cast hh
      have hh0 : (0 : ℝ) < h := by exact_mod_cast hhpos
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · rw [div_lt_iff₀ hMr]; nlinarith [Real.pi_pos]
    have hζh : ζ ^ h = cexp (I * ((2 * π * h / M : ℝ) : ℂ)) := by
      rw [hζdef, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hnz : ‖z - 1‖ = 2 * Real.sin (π * h / M) := by
      have e1 : z - 1 = -(ζ ^ h - 1) * z := by
        rw [hz]; field_simp; ring
      rw [e1, norm_mul, norm_neg, hzn, mul_one, hζh, Complex.norm_exp_I_mul_ofReal_sub_one,
        norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [show 2 * π * h / M / 2 = π * h / M by ring, abs_of_pos hs]
    have hz1n : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
    rw [hsum, norm_mul, norm_mul, hzn, one_mul, norm_div, norm_div, hnz, norm_one,
      Complex.norm_natCast]
    have hnum : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hzn]; norm_num
    calc 1 / (M : ℝ) * (‖z ^ N - 1‖ / (2 * Real.sin (π * h / M)))
        ≤ 1 / (M : ℝ) * (2 / (2 * Real.sin (π * h / M))) := by gcongr
      _ = 1 / (M * Real.sin (π * h / M)) := by field_simp

theorem fourier_split (M L N : ℕ) (hLM : L < M) (hNL : N ≤ L) (t : ℝ) :
    ‖S N t‖ ≤ ∑ h ∈ Finset.range M, w M L h * ‖A M L h t‖ := by
  set ζ := cexp (2 * π * I / M) with hζdef
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hLM
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  set c : ℕ → ℂ := fun n => (n : ℂ) ^ (-(1 / 2 : ℂ)) * (n : ℂ) ^ (-((t : ℂ) * I)) with hc
  have hA : ∀ h, A M L h t = ∑ n ∈ Finset.Icc 1 L, ζ ^ (h * n) * c n := by
    intro h
    unfold A DP
    apply Finset.sum_congr rfl
    intro n _
    rw [tw_eq, hc, mul_assoc]
  have hS : S N t = ∑ m ∈ Finset.Icc 1 N, c m := by
    unfold S
    apply Finset.sum_congr rfl
    intro n hn
    have : n ≠ 0 := by simp at hn; omega
    rw [cpow_split n this]
  have key : S N t = ∑ h ∈ Finset.range M,
      ((1 / (M : ℂ)) * ∑ m ∈ Finset.Icc 1 N, (ζ ^ m)⁻¹ ^ h) * A M L h t := by
    rw [hS]
    have step : ∀ m ∈ Finset.Icc 1 N, c m = ∑ n ∈ Finset.Icc 1 L,
        (1 / (M : ℂ)) * (∑ h ∈ Finset.range M, (ζ ^ m)⁻¹ ^ h * ζ ^ (h * n)) * c n := by
      intro m hm
      have hm' : m ∈ Finset.Icc 1 L := by
        simp only [Finset.mem_Icc] at hm ⊢; omega
      rw [Finset.sum_congr rfl (fun n hn => by
        rw [orth M hM n m (by simp only [Finset.mem_Icc] at hn; omega)
          (by simp only [Finset.mem_Icc] at hm; omega)])]
      simp only [mul_ite, ite_mul, mul_zero, zero_mul]
      rw [Finset.sum_ite_eq' (Finset.Icc 1 L) m, if_pos hm']
      field_simp
    rw [Finset.sum_congr rfl step]
    simp_rw [hA, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun n _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro n _
    apply Finset.sum_congr rfl; intro m _
    ring
  rw [key]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
  rw [norm_mul]
  gcongr
  exact D_bound M L N h hLM hNL (Finset.mem_range.mp hh)

end
end GuthMaynard.CitedZeros.FM.PartF
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM
noncomputable section
/-! ## (F) -/
alias fourier_split := GuthMaynard.CitedZeros.FM.PartF.fourier_split

alias weight_sum := GuthMaynard.CitedZeros.FM.PartF.weight_sum

end
end GuthMaynard.CitedZeros.FM
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM.PartM
open GuthMaynard.CitedZeros.FM
noncomputable section
/-! ## (H) power mean -/
theorem power_mean {ι : Type*} (s : Finset ι) (wt x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ wt i)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, wt i * x i) ^ 4 ≤ (∑ i ∈ s, wt i) ^ 3 * ∑ i ∈ s, wt i * x i ^ 4 := by
  have h1 : (∑ i ∈ s, wt i * x i) ^ 2 ≤ (∑ i ∈ s, wt i) * ∑ i ∈ s, wt i * x i ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
      (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)) (fun i hi => by nlinarith [hw i hi])
  have h2 : (∑ i ∈ s, wt i * x i ^ 2) ^ 2 ≤ (∑ i ∈ s, wt i) * ∑ i ∈ s, wt i * x i ^ 4 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
      (fun i hi => mul_nonneg (hw i hi) (by positivity)) (fun i hi => by nlinarith [hw i hi])
  have hW : 0 ≤ ∑ i ∈ s, wt i := Finset.sum_nonneg hw
  have hA : 0 ≤ ∑ i ∈ s, wt i * x i ^ 2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  calc (∑ i ∈ s, wt i * x i) ^ 4 = ((∑ i ∈ s, wt i * x i) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ i ∈ s, wt i) * ∑ i ∈ s, wt i * x i ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (∑ i ∈ s, wt i) ^ 2 * (∑ i ∈ s, wt i * x i ^ 2) ^ 2 := by ring
    _ ≤ (∑ i ∈ s, wt i) ^ 2 * ((∑ i ∈ s, wt i) * ∑ i ∈ s, wt i * x i ^ 4) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-! ## (M) fourth moment of a Dirichlet polynomial -/
/-- Conjugation of `k^{-it}`. -/
lemma conj_natCast_cpow (k : ℕ) (hk : k ≠ 0) (t : ℝ) :
    (starRingEnd ℂ) ((k : ℂ) ^ (-((t : ℂ) * I))) = (k : ℂ) ^ (I * t) := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [cpow_def_of_ne_zero hk', cpow_def_of_ne_zero hk', ← Complex.exp_conj]
  congr 1
  rw [map_mul, ← natCast_log, Complex.conj_ofReal, map_neg, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  ring

/-- Coefficient bound for a quadruple with `mn = m'n'`. -/
lemma quad_bound (a : ℕ → ℂ) (m n m' n' : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hm' : 1 ≤ m')
    (hn' : 1 ≤ n') (h : m * n = m' * n')
    (ham : ‖a m‖ ≤ (m : ℝ) ^ (-(1 / 2 : ℝ))) (han : ‖a n‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)))
    (ham' : ‖a m'‖ ≤ (m' : ℝ) ^ (-(1 / 2 : ℝ))) (han' : ‖a n'‖ ≤ (n' : ℝ) ^ (-(1 / 2 : ℝ))) :
    ‖a m‖ * ‖a n‖ * (‖a m'‖ * ‖a n'‖) ≤ 1 / ((m : ℝ) * n) := by
  have hmr : (0 : ℝ) ≤ m := by positivity
  have hnr : (0 : ℝ) ≤ n := by positivity
  have hmr' : (0 : ℝ) ≤ m' := by positivity
  have hnr' : (0 : ℝ) ≤ n' := by positivity
  have hpos : (0 : ℝ) < (m : ℝ) * n := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hcast : (m' : ℝ) * n' = (m : ℝ) * n := by exact_mod_cast h.symm
  calc ‖a m‖ * ‖a n‖ * (‖a m'‖ * ‖a n'‖)
      ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((m' : ℝ) ^ (-(1 / 2 : ℝ)) * (n' : ℝ) ^ (-(1 / 2 : ℝ))) := by
        gcongr
    _ = ((m : ℝ) * n) ^ (-(1 / 2 : ℝ)) * ((m : ℝ) * n) ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.mul_rpow hmr hnr, ← Real.mul_rpow hmr' hnr', hcast]
    _ = ((m : ℝ) * n) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hpos]; norm_num
    _ = 1 / ((m : ℝ) * n) := by rw [Real.rpow_neg_one, one_div]

/-- The quadruple sum `Σ_{mn = m'n'} 1/(mn)` is at most `H_L^4`. -/
lemma quad_sum_le (L : ℕ) :
    ∑ x ∈ ((Finset.Icc 1 L ×ˢ Finset.Icc 1 L) ×ˢ (Finset.Icc 1 L ×ˢ Finset.Icc 1 L)).filter
        (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2), 1 / ((x.1.1 : ℝ) * x.1.2) ≤
      (∑ i ∈ Finset.Icc 1 L, 1 / (i : ℝ)) ^ 4 := by
  set Ic := Finset.Icc 1 L
  set E := (Ic ×ˢ Ic) ×ˢ (Ic ×ˢ Ic)
  let ψ : (ℕ × ℕ) × (ℕ × ℕ) → (ℕ × ℕ) × (ℕ × ℕ) :=
    fun y => ((y.1.1 * y.1.2, y.2.1 * y.2.2), (y.1.1 * y.2.1, y.1.2 * y.2.2))
  have hsub : E.filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2) ⊆ E.image ψ := by
    rintro ⟨⟨m, n⟩, ⟨m', n'⟩⟩ hx
    simp only [Finset.mem_filter, E, Ic, Finset.mem_product, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨⟨hm1, hmL⟩, hn1, hnL⟩, ⟨hm1', hmL'⟩, hn1', hnL'⟩, h⟩ := hx
    set g := Nat.gcd m m' with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hm1
    set u := m / g
    set v := m' / g
    have hgu : g * u = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m m')
    have hgv : g * v = m' := Nat.mul_div_cancel' (Nat.gcd_dvd_right m m')
    have hcop : Nat.Coprime u v := Nat.coprime_div_gcd_div_gcd hg0
    have hun : u * n = v * n' := by
      apply Nat.eq_of_mul_eq_mul_left hg0
      calc g * (u * n) = (g * u) * n := by ring
        _ = m' * n' := by rw [hgu, h]
        _ = g * (v * n') := by rw [← hgv]; ring
    have hvn : v ∣ n := hcop.symm.dvd_of_dvd_mul_left ⟨n', hun⟩
    set w := n / v
    have hvw : v * w = n := Nat.mul_div_cancel' hvn
    have hv0 : 0 < v := Nat.pos_of_ne_zero (by rintro hv; rw [hv] at hgv; omega)
    have hu0 : 0 < u := Nat.pos_of_ne_zero (by rintro hu; rw [hu] at hgu; omega)
    have hw0 : 0 < w := Nat.pos_of_ne_zero (by rintro hw; rw [hw] at hvw; omega)
    have huw : u * w = n' := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg0 hv0)
      calc g * v * (u * w) = (g * u) * (v * w) := by ring
        _ = m' * n' := by rw [hgu, hvw, h]
        _ = g * v * n' := by rw [hgv]
    have hgL : g ≤ L := (Nat.gcd_le_left _ hm1).trans hmL
    have huL : u ≤ L := (Nat.div_le_self _ _).trans hmL
    have hvL : v ≤ L := (Nat.div_le_self _ _).trans hmL'
    have hwL : w ≤ L := (Nat.div_le_self _ _).trans hnL
    refine Finset.mem_image.mpr ⟨((g, u), (v, w)), ?_, ?_⟩
    · simp only [E, Ic, Finset.mem_product, Finset.mem_Icc]
      omega
    · simp only [ψ, hgu, hvw, hgv, huw]
  have hnn : ∀ x ∈ E.image ψ, 0 ≤ 1 / ((x.1.1 : ℝ) * x.1.2) := fun x _ => by positivity
  calc _ ≤ ∑ x ∈ E.image ψ, 1 / ((x.1.1 : ℝ) * x.1.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => hnn x hx)
    _ ≤ ∑ y ∈ E, 1 / (((ψ y).1.1 : ℝ) * (ψ y).1.2) :=
        Finset.sum_image_le_of_nonneg (fun x hx => hnn x hx)
    _ = ∑ y ∈ E, (1 / (y.1.1 : ℝ) * (1 / (y.1.2 : ℝ))) * (1 / (y.2.1 : ℝ) * (1 / (y.2.2 : ℝ))) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        simp only [ψ]; push_cast; field_simp
    _ = (∑ i ∈ Ic, 1 / (i : ℝ)) ^ 4 := by
        simp only [E, Finset.sum_product, pow_succ, pow_zero, one_mul, Finset.sum_mul,
          Finset.mul_sum, one_div]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem fourth_moment_poly (L : ℕ) (hL : 1 ≤ L) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Icc 1 L, ‖a n‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ))) (T₁ T₂ : ℝ) (hT : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, ‖DP a L t‖ ^ 4 ≤
      (T₂ - T₁ + 4 * (L : ℝ) ^ 2 * (1 + Real.log ((L : ℝ) ^ 2))) * (1 + Real.log L) ^ 4 := by
  set Ic := Finset.Icc 1 L
  set D := Ic ×ˢ Ic
  set K := Finset.Icc 1 (L ^ 2)
  let b : ℕ → ℂ := fun k => ∑ p ∈ D.filter (fun p => p.1 * p.2 = k), a p.1 * a p.2
  have hmaps : ∀ p ∈ D, p.1 * p.2 ∈ K := by
    intro p hp
    simp only [D, Ic, K, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    rw [sq]; exact Nat.mul_le_mul hp.1.2 hp.2.2
  have hsq : ∀ t : ℝ, DP a L t ^ 2 = ∑ k ∈ K, b k * (k : ℂ) ^ (-((t : ℂ) * I)) := by
    intro t
    rw [sq, DP, Finset.sum_mul_sum, ← Finset.sum_product']
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [b, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [(Finset.mem_filter.mp hp).2.symm]
    push_cast
    rw [natCast_mul_natCast_cpow]; ring
  have hconj : ∀ t : ℝ, ‖DP a L t‖ ^ 4 =
      ‖∑ k ∈ K, (starRingEnd ℂ) (b k) * (k : ℂ) ^ (I * t)‖ ^ 2 := by
    intro t
    have : ∑ k ∈ K, (starRingEnd ℂ) (b k) * (k : ℂ) ^ (I * t) =
        (starRingEnd ℂ) (DP a L t ^ 2) := by
      rw [hsq, map_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk0 : k ≠ 0 := by simp only [K, Finset.mem_Icc] at hk; omega
      rw [map_mul, conj_natCast_cpow k hk0]
    rw [this, RCLike.norm_conj, norm_pow]; ring
  have hs : ∀ n ∈ K, 1 ≤ n ∧ n ≤ L ^ 2 := fun n hn => Finset.mem_Icc.mp hn
  have hmv := (ArtinPrimitiveRoots.dirichlet_mean_value K (L ^ 2) hs
    (fun k => (starRingEnd ℂ) (b k))).1 T₁ T₂ hT
  -- coefficient bound
  let α : ℕ × ℕ → ℝ := fun p => ‖a p.1‖ * ‖a p.2‖
  set Q := (D ×ˢ D).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)
  have hA : ∑ k ∈ K, (∑ p ∈ D.filter (fun p => p.1 * p.2 = k), α p) ^ 2 =
      ∑ x ∈ Q, α x.1 * α x.2 := by
    have hmapsQ : ∀ x ∈ Q, x.1.1 * x.1.2 ∈ K := fun x hx =>
      hmaps x.1 (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
    rw [← Finset.sum_fiberwise_of_maps_to hmapsQ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext ⟨p, q⟩
    simp only [Q, Finset.mem_product, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, hpk⟩, hq, hqk⟩
      exact ⟨⟨⟨hp, hq⟩, hpk.trans hqk.symm⟩, hpk⟩
    · rintro ⟨⟨⟨hp, hq⟩, hpq⟩, hpk⟩
      exact ⟨⟨hp, hpk⟩, hq, hpq.symm.trans hpk⟩
  have hB : ∑ x ∈ Q, α x.1 * α x.2 ≤ ∑ x ∈ Q, 1 / ((x.1.1 : ℝ) * x.1.2) := by
    refine Finset.sum_le_sum (fun x hx => ?_)
    simp only [Q, D, Ic, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨⟨hm1, hmL⟩, hn1, hnL⟩, ⟨hm1', hmL'⟩, hn1', hnL'⟩, h⟩ := hx
    have hI : ∀ n, 1 ≤ n → n ≤ L → n ∈ Ic := fun n h1 h2 => Finset.mem_Icc.mpr ⟨h1, h2⟩
    exact quad_bound a _ _ _ _ hm1 hn1 hm1' hn1' h (ha _ (hI _ hm1 hmL)) (ha _ (hI _ hn1 hnL))
      (ha _ (hI _ hm1' hmL')) (ha _ (hI _ hn1' hnL'))
  have hH : ∑ i ∈ Ic, 1 / (i : ℝ) ≤ 1 + Real.log L := by
    have := harmonic_le_one_add_log L
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at this
    simpa [one_div] using this
  have hcoef : ∑ k ∈ K, ‖(starRingEnd ℂ) (b k)‖ ^ 2 ≤ (1 + Real.log L) ^ 4 := by
    calc ∑ k ∈ K, ‖(starRingEnd ℂ) (b k)‖ ^ 2
        ≤ ∑ k ∈ K, (∑ p ∈ D.filter (fun p => p.1 * p.2 = k), α p) ^ 2 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [RCLike.norm_conj]
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp only [α, norm_mul]
      _ = ∑ x ∈ Q, α x.1 * α x.2 := hA
      _ ≤ _ := hB
      _ ≤ (∑ i ∈ Ic, 1 / (i : ℝ)) ^ 4 := quad_sum_le L
      _ ≤ (1 + Real.log L) ^ 4 :=
          pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => by positivity)) hH 4
  have hfac : 0 ≤ T₂ - T₁ + 4 * ((L ^ 2 : ℕ) : ℝ) * (1 + Real.log ((L ^ 2 : ℕ) : ℝ)) := by
    have : 0 ≤ Real.log ((L ^ 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have : 0 ≤ T₂ - T₁ := by linarith
    positivity
  calc ∫ t in T₁..T₂, ‖DP a L t‖ ^ 4
      = ∫ t in T₁..T₂, ‖∑ k ∈ K, (starRingEnd ℂ) (b k) * (k : ℂ) ^ (I * t)‖ ^ 2 := by
        simp_rw [hconj]
    _ ≤ (T₂ - T₁ + 4 * ((L ^ 2 : ℕ) : ℝ) * (1 + Real.log ((L ^ 2 : ℕ) : ℝ))) *
          ∑ k ∈ K, ‖(starRingEnd ℂ) (b k)‖ ^ 2 := hmv
    _ ≤ (T₂ - T₁ + 4 * ((L ^ 2 : ℕ) : ℝ) * (1 + Real.log ((L ^ 2 : ℕ) : ℝ))) *
          (1 + Real.log L) ^ 4 := mul_le_mul_of_nonneg_left hcoef hfac
    _ = _ := by push_cast; ring

end
end GuthMaynard.CitedZeros.FM.PartM
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM
noncomputable section
/-! ## (M) and (H) -/
alias fourth_moment_poly := GuthMaynard.CitedZeros.FM.PartM.fourth_moment_poly

alias power_mean := GuthMaynard.CitedZeros.FM.PartM.power_mean

end
end GuthMaynard.CitedZeros.FM
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
open GuthMaynard.CitedZeros.FM
namespace GuthMaynard.CitedZeros.FM.PartD
noncomputable section
lemma zeta_cont : Continuous (fun t : ℝ => riemannZeta (1 / 2 + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have h : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => 1 / 2 + (t : ℂ) * I)
    (differentiableAt_riemannZeta h).continuousAt (by fun_prop)

lemma zeta4_cont : Continuous (fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖ ^ 4) :=
  (continuous_norm.comp zeta_cont).pow 4

lemma A_cont (M L h : ℕ) : Continuous (fun t : ℝ => A M L h t) := by
  unfold A DP
  apply continuous_finsetSum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.1 hn).1
    exact_mod_cast (by omega : n ≠ 0)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))

lemma tw_norm (M h L n : ℕ) (hn : n ∈ Finset.Icc 1 L) :
    ‖tw M h n‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hn1 : 0 < n := (Finset.mem_Icc.1 hn).1
  unfold tw
  have : (2 * π * I * ((h * n : ℕ) : ℂ) / M) = ((2 * π * (h * n : ℕ) / M : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, Complex.norm_natCast_cpow_of_pos hn1]
  simp

lemma four_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [mul_nonneg (sq_nonneg (a - b)) (add_nonneg (add_nonneg
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 7) (sq_nonneg a))
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) (mul_nonneg ha hb)))
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 7) (sq_nonneg b)))]

lemma pointwise (L : ℕ) (t : ℝ) (ht : 509 ≤ t) (hNL : RSInt.rsNn t ≤ L)
    (hgood : 0 < RSInt.rsFrac t ∧ Real.cos (2 * π * RSInt.rsFrac t) ≠ 0) :
    ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤
      128 * (∑ h ∈ Finset.range (L + 1), w (L + 1) L h) ^ 3 *
        (∑ h ∈ Finset.range (L + 1), w (L + 1) L h * ‖A (L + 1) L h t‖ ^ 4) + 648 := by
  have h1 := rs_pointwise t ht hgood.1 hgood.2
  have h2 := fourier_split (L + 1) L _ (Nat.lt_succ_self L) hNL t
  have hw : ∀ h ∈ Finset.range (L + 1), 0 ≤ w (L + 1) L h :=
    fun h hh => w_nonneg _ _ _ (Finset.mem_range.1 hh)
  have h3 := power_mean (Finset.range (L + 1)) (w (L + 1) L) (fun h => ‖A (L + 1) L h t‖) hw
    (fun _ _ => norm_nonneg _)
  set X := ∑ h ∈ Finset.range (L + 1), w (L + 1) L h * ‖A (L + 1) L h t‖
  have hX : 0 ≤ X := Finset.sum_nonneg fun h hh => mul_nonneg (hw h hh) (norm_nonneg _)
  have h4 : ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤ (2 * X + 3) ^ 4 := by
    apply pow_le_pow_left₀ (norm_nonneg _); linarith
  have h5 := four_le (2 * X) 3 (by linarith) (by norm_num)
  have h6 : (2 * X) ^ 4 = 16 * X ^ 4 := by ring
  linarith

/-- The dyadic block with the exponent 9 that the stubs actually give. -/
theorem dyadic_block9 : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 509 ≤ T →
    ∫ t in T..(2 * T), ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤ C * T * (1 + Real.log T) ^ 9 := by
  refine ⟨10888, by norm_num, fun T hT => ?_⟩
  set L := RSInt.rsNn (2 * T) with hLdef
  have hpi : 3 < π := Real.pi_gt_three
  have hpi4 : π < 4 := Real.pi_lt_four
  have hαsq : RSInt.rsAlpha (2 * T) ^ 2 = T / π := by
    unfold RSInt.rsAlpha
    rw [Real.sq_sqrt (by positivity)]; field_simp
  have hα0 : 0 ≤ RSInt.rsAlpha (2 * T) := Real.sqrt_nonneg _
  have hL2 : 2 ≤ L := by
    apply Nat.le_floor
    have : (4 : ℝ) ≤ RSInt.rsAlpha (2 * T) ^ 2 := by
      rw [hαsq, le_div_iff₀ (by positivity)]; nlinarith
    push_cast
    nlinarith
  have hLle : (L : ℝ) ≤ RSInt.rsAlpha (2 * T) := Nat.floor_le hα0
  have hL2r : (2 : ℝ) ≤ L := by exact_mod_cast hL2
  have hLsq : (L : ℝ) ^ 2 ≤ T := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg L) hLle 2
    rw [hαsq] at this
    exact this.trans (div_le_self (by linarith) (by linarith))
  have hL1T : (L : ℝ) + 1 ≤ T := by nlinarith
  have hLT : (L : ℝ) ≤ T := by linarith
  -- monotonicity of rsNn
  have hmono : ∀ t, t ≤ 2 * T → RSInt.rsNn t ≤ L := by
    intro t ht
    unfold RSInt.rsNn RSInt.rsAlpha at *
    apply Nat.floor_mono
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right ht (by positivity)
  set W := ∑ h ∈ Finset.range (L + 1), w (L + 1) L h with hWdef
  have hw : ∀ h ∈ Finset.range (L + 1), 0 ≤ w (L + 1) L h :=
    fun h hh => w_nonneg _ _ _ (Finset.mem_range.1 hh)
  have hW0 : 0 ≤ W := Finset.sum_nonneg hw
  set g : ℝ → ℝ := fun t =>
    128 * W ^ 3 * (∑ h ∈ Finset.range (L + 1), w (L + 1) L h * ‖A (L + 1) L h t‖ ^ 4) + 648
    with hgdef
  have hAi : ∀ h, IntervalIntegrable (fun t => w (L + 1) L h * ‖A (L + 1) L h t‖ ^ 4)
      volume T (2 * T) := fun h =>
    (continuous_const.mul ((continuous_norm.comp (A_cont _ _ h)).pow 4)).intervalIntegrable _ _
  have hgc : Continuous g := by
    rw [hgdef]
    refine Continuous.add (continuous_const.mul (continuous_finsetSum _ fun h _ => ?_))
      continuous_const
    exact continuous_const.mul ((continuous_norm.comp (A_cont _ _ h)).pow 4)
  have hTT : T ≤ 2 * T := by linarith
  have step1 : ∫ t in T..(2 * T), ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤ ∫ t in T..(2 * T), g t := by
    apply intervalIntegral.integral_mono_ae_restrict hTT (zeta4_cont.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (bad_countable.ae_notMem volume)] with t ht hb
    have ht509 : 509 ≤ t := by linarith [ht.1]
    have hgood : 0 < RSInt.rsFrac t ∧ Real.cos (2 * π * RSInt.rsFrac t) ≠ 0 := by
      by_contra hc
      exact hb ⟨ht509, hc⟩
    exact pointwise L t ht509 (hmono t ht.2) hgood
  set B : ℝ := (2 * T - T + 4 * (L : ℝ) ^ 2 * (1 + Real.log ((L : ℝ) ^ 2))) *
    (1 + Real.log L) ^ 4 with hBdef
  have hAB : ∀ h, ∫ t in T..(2 * T), ‖A (L + 1) L h t‖ ^ 4 ≤ B := fun h =>
    fourth_moment_poly L (by omega) (tw (L + 1) h) (fun n hn => tw_norm _ _ L n hn) T (2 * T) hTT
  have step2 : ∫ t in T..(2 * T), g t ≤ 128 * W ^ 4 * B + 648 * T := by
    rw [hgdef]
    simp only
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum, intervalIntegral.integral_const]
    · have : ∑ h ∈ Finset.range (L + 1), ∫ t in T..(2 * T), w (L + 1) L h * ‖A (L + 1) L h t‖ ^ 4
          ≤ W * B := by
        rw [hWdef, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro h hh
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hAB h) (hw h hh)
      have h128 : 0 ≤ 128 * W ^ 3 := by positivity
      have := mul_le_mul_of_nonneg_left this h128
      simp only [smul_eq_mul]
      nlinarith
    · exact fun h _ => hAi h
    · exact (continuous_const.mul (continuous_finsetSum _ fun h _ =>
        continuous_const.mul ((continuous_norm.comp (A_cont _ _ h)).pow 4))).intervalIntegrable _ _
    · exact intervalIntegrable_const
  -- numerical bounds
  have hT1 : (1 : ℝ) ≤ T := by linarith
  set ℓ := 1 + Real.log T with hℓ
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hWle : W ≤ 2 * ℓ := by
    have h1 := weight_sum L (by omega)
    have h2 : Real.log ((L : ℝ) + 1) ≤ Real.log T := Real.log_le_log (by linarith) hL1T
    rw [hWdef]; linarith
  have hlogL : Real.log L ≤ Real.log T := Real.log_le_log hL0 hLT
  have hlogL2 : Real.log ((L : ℝ) ^ 2) ≤ Real.log T := Real.log_le_log (by positivity) hLsq
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hB : B ≤ 5 * T * ℓ ^ 5 := by
    rw [hBdef]
    have e1 : 2 * T - T + 4 * (L : ℝ) ^ 2 * (1 + Real.log ((L : ℝ) ^ 2)) ≤ 5 * T * ℓ := by
      have : 4 * (L : ℝ) ^ 2 * (1 + Real.log ((L : ℝ) ^ 2)) ≤ 4 * T * ℓ := by
        have hl2 : 0 ≤ 1 + Real.log ((L : ℝ) ^ 2) := by
          have := Real.log_nonneg (one_le_pow₀ (n := 2) (by linarith : (1:ℝ) ≤ L)); linarith
        have := mul_le_mul hLsq (by linarith : 1 + Real.log ((L : ℝ) ^ 2) ≤ ℓ) hl2 (by linarith)
        linarith
      nlinarith
    have e2 : (1 + Real.log L) ^ 4 ≤ ℓ ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    have e3 : 0 ≤ 2 * T - T + 4 * (L : ℝ) ^ 2 * (1 + Real.log ((L : ℝ) ^ 2)) := by
      have := Real.log_nonneg (one_le_pow₀ (n := 2) (by linarith : (1:ℝ) ≤ L))
      positivity
    calc _ ≤ (5 * T * ℓ) * ℓ ^ 4 := mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = 5 * T * ℓ ^ 5 := by ring
  have hW4 : W ^ 4 ≤ 16 * ℓ ^ 4 := by
    calc W ^ 4 ≤ (2 * ℓ) ^ 4 := pow_le_pow_left₀ hW0 hWle 4
      _ = 16 * ℓ ^ 4 := by ring
  have hB0 : 0 ≤ B := by
    have := hAB 0
    have h0 : 0 ≤ ∫ t in T..(2 * T), ‖A (L + 1) L 0 t‖ ^ 4 :=
      intervalIntegral.integral_nonneg hTT (fun _ _ => by positivity)
    linarith
  have hfin : 128 * W ^ 4 * B ≤ 128 * (16 * ℓ ^ 4) * (5 * T * ℓ ^ 5) := by
    apply mul_le_mul (by linarith) hB hB0 (by positivity)
  have hℓ9 : 1 ≤ ℓ ^ 9 := one_le_pow₀ hℓ1
  have : 648 * T ≤ 648 * T * ℓ ^ 9 := by nlinarith
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ 128 * (16 * ℓ ^ 4) * (5 * T * ℓ ^ 5) + 648 * T * ℓ ^ 9 := by linarith
    _ = 10888 * T * ℓ ^ 9 := by ring

lemma ell_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (1 + Real.log a) ^ 9 ≤ (1 + Real.log b) ^ 9 := by
  have h1 := Real.log_nonneg ha
  have h2 := Real.log_le_log (by linarith) hab
  exact pow_le_pow_left₀ (by linarith) (by linarith) 9

lemma tail9 (C : ℝ) (hC : 0 ≤ C) (hd : ∀ T : ℝ, 509 ≤ T →
    ∫ t in T..(2 * T), ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤ C * T * (1 + Real.log T) ^ 9) :
    ∀ n : ℕ, ∀ T : ℝ, 509 ≤ T → T ≤ 509 * 2 ^ (n + 1) →
      ∫ t in (509 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤ 2 * C * T * (1 + Real.log T) ^ 9 := by
  have hsub : ∀ T U : ℝ, 509 ≤ T → T ≤ U → U ≤ 2 * T →
      ∫ t in T..U, ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤ C * T * (1 + Real.log T) ^ 9 := by
    intro T U hT hTU hU
    refine le_trans ?_ (hd T hT)
    exact intervalIntegral.integral_mono_interval le_rfl hTU hU
      (ae_of_all _ fun _ => by positivity) (zeta4_cont.intervalIntegrable _ _)
  intro n
  induction n with
  | zero =>
    intro T hT hT2
    have h := hsub 509 T le_rfl hT (by norm_num at hT2 ⊢; linarith)
    have hm := ell_mono (by norm_num : (1:ℝ) ≤ 509) hT
    have hl : 0 ≤ (1 + Real.log 509) ^ 9 := by
      have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 509); positivity
    have : C * 509 * (1 + Real.log 509) ^ 9 ≤ 2 * C * T * (1 + Real.log T) ^ 9 := by
      have := mul_le_mul (by linarith : (509:ℝ) ≤ 2 * T) hm hl (by linarith)
      nlinarith
    linarith
  | succ n ih =>
    intro T hT hT2
    by_cases hc : T ≤ 509 * 2 ^ (n + 1)
    · exact ih T hT hc
    replace hc := not_le.mp hc
    have hp : (509 : ℝ) ≤ 509 * 2 ^ n := by
      have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      linarith
    have hT2' : (509 : ℝ) ≤ T / 2 := by
      rw [pow_succ] at hc; linarith
    have hT2'' : T / 2 ≤ 509 * 2 ^ (n + 1) := by
      rw [pow_succ] at hT2 ⊢; rw [pow_succ] at hT2; linarith
    have h1 := ih (T / 2) hT2' hT2''
    have h2 := hsub (T / 2) T hT2' (by linarith) (by linarith)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (zeta4_cont.intervalIntegrable (μ := volume) 509 (T / 2))
      (zeta4_cont.intervalIntegrable (μ := volume) (T / 2) T)
    have hm := ell_mono (by linarith : (1:ℝ) ≤ T / 2) (by linarith : T / 2 ≤ T)
    have hl : 0 ≤ (1 + Real.log (T / 2)) ^ 9 := by
      have := Real.log_nonneg (by linarith : (1:ℝ) ≤ T / 2); positivity
    have : 3 * C * (T / 2) * (1 + Real.log (T / 2)) ^ 9 ≤ 2 * C * T * (1 + Real.log T) ^ 9 := by
      have := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 3 * C * (T / 2))
      have hl' : 0 ≤ C * T * (1 + Real.log T) ^ 9 := by
        have := Real.log_nonneg (by linarith : (1:ℝ) ≤ T); positivity
      nlinarith
    linarith

/-- The initial bound with the exponent 9 that the stubs actually give. -/
theorem initial_bound9 : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤ C * T * (1 + Real.log T) ^ 9 := by
  obtain ⟨C₀, hC₀, hd⟩ := dyadic_block9
  set K := ∫ t in (0 : ℝ)..509, ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 with hK
  have hK0 : 0 ≤ K := intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => by positivity)
  refine ⟨K / 2 + 2 * C₀, by positivity, fun T hT => ?_⟩
  have hlog := Real.log_nonneg (by linarith : (1:ℝ) ≤ T)
  have hl9 : 1 ≤ (1 + Real.log T) ^ 9 := one_le_pow₀ (by linarith)
  have hKle : K ≤ K / 2 * T * (1 + Real.log T) ^ 9 := by
    have : 2 ≤ T * (1 + Real.log T) ^ 9 := by nlinarith
    nlinarith
  have hpos : 0 ≤ 2 * C₀ * T * (1 + Real.log T) ^ 9 := by
    have := (by linarith : (0:ℝ) ≤ T); positivity
  by_cases hc : T ≤ 509
  · have : ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 ≤ K :=
      intervalIntegral.integral_mono_interval le_rfl (by linarith) hc
        (ae_of_all _ fun _ => by positivity) (zeta4_cont.intervalIntegrable _ _)
    nlinarith
  replace hc := not_le.mp hc
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (T / 509) (by norm_num : (1:ℝ) < 2)
  have hTn : T ≤ 509 * 2 ^ (n + 1) := by
    rw [div_lt_iff₀ (by norm_num)] at hn
    have : (2:ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have h1 := tail9 C₀ hC₀ hd n T hc.le hTn
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (zeta4_cont.intervalIntegrable (μ := volume) 0 509)
    (zeta4_cont.intervalIntegrable (μ := volume) 509 T)
  rw [← hadd]
  nlinarith

theorem moment_bound_of_k_le_two (k : ℕ) (hk : k = 1 ∨ k = 2) (ε : ℝ) (hε : 0 < ε) :
    (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k))
      =O[atTop] (fun T : ℝ => T ^ ε) := by
  obtain ⟨C, hC, hb⟩ := initial_bound9
  have hlog := (isLittleO_log_rpow_rpow_atTop (9 : ℝ) hε).isBigO
  refine IsBigO.trans ?_ hlog
  apply IsBigO.of_bound ((1 + C) * 2 ^ 9)
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
  have hpt : ∀ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k) ≤
      1 + ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 := by
    intro t
    have hx : 0 ≤ ‖riemannZeta (1 / 2 + t * I)‖ := norm_nonneg _
    rcases hk with rfl | rfl
    · nlinarith [sq_nonneg (‖riemannZeta (1 / 2 + t * I)‖ ^ 2 - 1)]
    · norm_num
  have hc2k : Continuous (fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k)) :=
    (continuous_norm.comp zeta_cont).pow _
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k) :=
    intervalIntegral.integral_nonneg hT0 (fun _ _ => by positivity)
  have hI : ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k) ≤
      T + C * T * (1 + Real.log T) ^ 9 := by
    calc _ ≤ ∫ t in (0 : ℝ)..T, (1 + ‖riemannZeta (1 / 2 + t * I)‖ ^ 4) :=
          intervalIntegral.integral_mono_on hT0 (hc2k.intervalIntegrable _ _)
            ((continuous_const.add zeta4_cont).intervalIntegrable _ _) (fun t _ => hpt t)
      _ = T + ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 := by
          rw [intervalIntegral.integral_add intervalIntegrable_const
            (zeta4_cont.intervalIntegrable _ _), intervalIntegral.integral_const]
          simp
      _ ≤ _ := by linarith [hb T (by linarith)]
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hl9 : 1 ≤ (1 + Real.log T) ^ 9 := one_le_pow₀ (by linarith)
  have h2l : (1 + Real.log T) ^ 9 ≤ 2 ^ 9 * Real.log T ^ 9 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) 9
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hTp : 0 < T := by linarith
  have step : 1 / T * ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k) ≤
      1 + C * (1 + Real.log T) ^ 9 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hTp]
    nlinarith
  have : 1 + C * (1 + Real.log T) ^ 9 ≤ (1 + C) * (1 + Real.log T) ^ 9 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2l (by linarith : (0:ℝ) ≤ 1 + C)
  nlinarith

end
end GuthMaynard.CitedZeros.FM.PartD
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
namespace GuthMaynard.CitedZeros.FM
noncomputable section
/-! ## (D) -/
alias moment_bound_of_k_le_two := GuthMaynard.CitedZeros.FM.PartD.moment_bound_of_k_le_two

end
end GuthMaynard.CitedZeros.FM
end

section
open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Real
open GuthMaynard
open GuthMaynard.CitedZeros
open GuthMaynard.CitedZeros.FM
noncomputable section
theorem solution (k : ℕ) (hk : k = 1 ∨ k = 2) (ε : ℝ) (hε : 0 < ε) :
    (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k))
      =O[atTop] (fun T : ℝ => T ^ ε) := by
  exact GuthMaynard.CitedZeros.FM.moment_bound_of_k_le_two k hk ε hε
end
end
