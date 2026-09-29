-- Prove2me | solution 1 for MeanSquare.eq_zero_of_re_lt_one_half_or_log_of_liminf_sub_one_mul_lintegral_cpow_log_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a7f44d3d-2832-58a8-b960-5622ff1e8452

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeanSquare_eq_zero_of_re_lt_one_half_or_log_of_liminf_sub_one_mul_lintegral_cpow_log_sq_le

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace KcMeanSquare

noncomputable def antider (s : ℂ) : ℕ → ℝ → ℂ
  | 0, u => -Complex.exp (-s * u) / s
  | N + 1, u => -((u : ℂ) ^ (N + 1) * Complex.exp (-s * u)) / s + ((N + 1 : ℂ) / s) * antider s N u

lemma hasDerivAt_exp_neg_mul (s : ℂ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (-s * x)) (-s * Complex.exp (-s * u)) u := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-s * z)) (Complex.exp (-s * u) * (-s)) (u : ℂ) := by
    have hm : HasDerivAt (fun z : ℂ => -s * z) (-s) (u : ℂ) := by
      simpa using (hasDerivAt_id (u : ℂ)).const_mul (-s)
    exact (Complex.hasDerivAt_exp (-s * u)).comp (u : ℂ) hm
  have h2 := h1.comp_ofReal
  simpa [mul_comm] using h2

lemma hasDerivAt_pow_mul_exp (s : ℂ) (N : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ (N + 1) * Complex.exp (-s * x))
      (((N + 1 : ℕ) : ℂ) * (u : ℂ) ^ N * Complex.exp (-s * u) +
        (u : ℂ) ^ (N + 1) * (-s * Complex.exp (-s * u))) u := by
  have hp : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (N + 1)) (((N + 1 : ℕ) : ℂ) * (u : ℂ) ^ N) u := by
    have h1 : HasDerivAt (fun z : ℂ => z ^ (N + 1)) (((N + 1 : ℕ) : ℂ) * (u : ℂ) ^ (N + 1 - 1)) (u : ℂ) :=
      hasDerivAt_pow (N + 1) (u : ℂ)
    simpa using h1.comp_ofReal
  exact hp.mul (hasDerivAt_exp_neg_mul s u)

lemma hasDerivAt_antider (s : ℂ) (hs : s ≠ 0) :
    ∀ N : ℕ, ∀ u : ℝ, HasDerivAt (antider s N) ((u : ℂ) ^ N * Complex.exp (-s * u)) u := by
  intro N
  induction N with
  | zero =>
    intro u
    have h := ((hasDerivAt_exp_neg_mul s u).neg).div_const s
    have h' : HasDerivAt (antider s 0) (-(-s * Complex.exp (-s * u)) / s) u :=
      h.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp [antider])
    convert h' using 1
    field_simp
  | succ N ih =>
    intro u
    have h1 := ((hasDerivAt_pow_mul_exp s N u).neg).div_const s
    have h2 := (ih u).const_mul ((N + 1 : ℂ) / s)
    have h := h1.add h2
    have h' : HasDerivAt (antider s (N + 1)) _ u :=
      h.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp [antider])
    convert h' using 1
    push_cast
    field_simp
    ring

lemma antider_zero (s : ℂ) (hs : s ≠ 0) :
    ∀ N : ℕ, antider s N 0 = -((N.factorial : ℂ) / s ^ (N + 1)) := by
  intro N
  induction N with
  | zero => simp [antider, div_eq_mul_inv]
  | succ N ih =>
    simp only [antider, ih]
    push_cast
    field_simp
    push_cast [Nat.factorial_succ]
    ring

lemma tendsto_pow_mul_exp_neg_mul (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    Tendsto (fun u : ℝ => (u : ℂ) ^ N * Complex.exp (-s * u)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).comp
    (tendsto_id.const_mul_atTop hs : Tendsto (fun u : ℝ => s.re * u) atTop atTop)
  have h2 : Tendsto (fun u : ℝ => (s.re ^ N)⁻¹ * ((s.re * u) ^ N * Real.exp (-(s.re * u)))) atTop
      (𝓝 ((s.re ^ N)⁻¹ * 0)) := h.const_mul _
  rw [mul_zero] at h2
  refine (tendsto_congr' ?_).mp h2
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  have hre : (-s * (u : ℂ)).re = -(s.re * u) := by
    simp [Complex.mul_re]
  rw [hre, mul_pow]
  have hsn : s.re ^ N ≠ 0 := pow_ne_zero _ hs.ne'
  field_simp

lemma tendsto_antider (s : ℂ) (hs : 0 < s.re) :
    ∀ N : ℕ, Tendsto (antider s N) atTop (𝓝 0) := by
  intro N
  induction N with
  | zero =>
    have h := ((tendsto_pow_mul_exp_neg_mul s hs 0).neg).div_const s
    simp only [pow_zero, one_mul, neg_zero, zero_div] at h
    refine (tendsto_congr ?_).mp h
    intro u; simp [antider]
  | succ N ih =>
    have h1 := ((tendsto_pow_mul_exp_neg_mul s hs (N + 1)).neg).div_const s
    have h2 := ih.const_mul ((N + 1 : ℂ) / s)
    have h := h1.add h2
    simp only [neg_zero, zero_div, mul_zero, add_zero] at h
    refine (tendsto_congr ?_).mp h
    intro u; simp [antider]

lemma norm_pow_mul_exp (s : ℂ) (N : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ‖(u : ℂ) ^ N * Complex.exp (-s * u)‖ = u ^ N * Real.exp (-s.re * u) := by
  rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  congr 2
  simp [Complex.mul_re]

lemma integrableOn_pow_mul_exp (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ N * Complex.exp (-s * u)) (Ioi 0) := by
  have hreal : IntegrableOn (fun x : ℝ => x ^ (N : ℝ) * Real.exp (-s.re * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith) one_pos hs
  have hcont : Continuous (fun u : ℝ => (u : ℂ) ^ N * Complex.exp (-s * u)) := by
    fun_prop
  refine Integrable.mono' hreal hcont.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ ?_)
  intro u hu
  rw [norm_pow_mul_exp s N u (le_of_lt hu), Real.rpow_natCast, Real.rpow_one]

theorem integral_pow_mul_exp (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ N * Complex.exp (-s * u) = (N.factorial : ℂ) / s ^ (N + 1) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun u _ => hasDerivAt_antider s hs0 N u) (integrableOn_pow_mul_exp s hs N)
    (tendsto_antider s hs N)
  rw [h, antider_zero s hs0 N]
  ring

variable {n J : ℕ}

noncomputable def mfun (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (y : ℝ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin J, d i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))

noncomputable def bcoef (d : Fin n → Fin J → ℂ) (p : Fin n × Fin J) : ℂ := d p.1 p.2 * (-1) ^ (p.2 : ℕ)

noncomputable def wexp (e : Fin n → ℂ) (r : ℝ) (p : Fin n × Fin J) : ℂ := e p.1 - r

noncomputable def supp (d : Fin n → Fin J → ℂ) : Finset (Fin n × Fin J) :=
  Finset.univ.filter (fun p => d p.1 p.2 ≠ 0)

noncomputable def Gfun (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r : ℝ) (u : ℝ) : ℂ :=
  ∑ p ∈ supp d, bcoef d p * (u : ℂ) ^ (p.2 : ℕ) * Complex.exp (-(u : ℂ) * wexp e r p)

lemma mem_supp {d : Fin n → Fin J → ℂ} {p : Fin n × Fin J} : p ∈ supp d ↔ d p.1 p.2 ≠ 0 := by
  simp [supp]

lemma ofReal_exp_neg_cpow (u : ℝ) (z : ℂ) :
    ((Real.exp (-u) : ℝ) : ℂ) ^ z = Complex.exp (-(u : ℂ) * z) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp]
  · push_cast; ring_nf
  · simp [Real.pi_pos]
  · simp [Real.pi_pos.le]

lemma mfun_exp_neg (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r : ℝ) (u : ℝ) :
    mfun e d (Real.exp (-u)) = Complex.exp (-(u : ℂ) * r) * Gfun e d r u := by
  unfold mfun Gfun
  rw [Real.log_exp, Finset.mul_sum]
  rw [← Finset.sum_product' (f := fun i j => d i j *
      ((((Real.exp (-u) : ℝ) : ℂ)) ^ e i * (((-u : ℝ) : ℂ)) ^ ((j : Fin J) : ℕ)))]
  rw [Finset.univ_product_univ]
  unfold supp
  rw [Finset.sum_filter_of_ne]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [ofReal_exp_neg_cpow]
    unfold bcoef wexp
    have hexp : Complex.exp (-(u : ℂ) * e p.1) =
        Complex.exp (-(u : ℂ) * r) * Complex.exp (-(u : ℂ) * (e p.1 - r)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hexp]
    push_cast
    ring
  · intro p _ hp h0
    apply hp
    simp [bcoef, h0]

lemma norm_mfun_exp_neg (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r : ℝ) (u : ℝ) :
    ‖mfun e d (Real.exp (-u))‖ = Real.exp (-r * u) * ‖Gfun e d r u‖ := by
  rw [mfun_exp_neg e d r u, norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]
  ring

lemma image_exp_neg_Ioi : (fun u : ℝ => Real.exp (-u)) '' Ioi 0 = Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    rw [Real.exp_lt_one_iff]
    simpa using hu
  · rintro ⟨hy0, hy1⟩
    refine ⟨-Real.log y, ?_, ?_⟩
    · have := Real.log_neg hy0 hy1
      simp only [mem_Ioi]; linarith
    · simp [Real.exp_log hy0]

lemma nnnorm_sq_eq_ofReal (z : ℂ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ← enorm_eq_nnnorm, ← ofReal_norm]

lemma lintegral_change (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r σ : ℝ) :
    ∫⁻ y in Ioc (0 : ℝ) 1, (‖mfun e d y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (y ^ (σ - 3)) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (‖Gfun e d r u‖ ^ 2 * Real.exp (-(σ - 2 + 2 * r) * u)) := by
  have hswap : ∫⁻ y in Ioc (0 : ℝ) 1, (‖mfun e d y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (y ^ (σ - 3)) =
      ∫⁻ y in Ioo (0 : ℝ) 1, (‖mfun e d y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (y ^ (σ - 3)) :=
    setLIntegral_congr Ioo_ae_eq_Ioc.symm
  rw [hswap, ← image_exp_neg_Ioi]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f := fun u : ℝ => Real.exp (-u)) (f' := fun u : ℝ => -Real.exp (-u))]
  · refine setLIntegral_congr_fun measurableSet_Ioi ?_
    intro u hu
    simp only
    rw [nnnorm_sq_eq_ofReal, norm_mfun_exp_neg e d r u,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Real.exp (-r * u) * ‖Gfun e d r u‖) ^ 2),
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [abs_neg, abs_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_pow, ← Real.exp_nat_mul]
    have : Real.exp (-u) * (Real.exp (2 * (-r * u)) * ‖Gfun e d r u‖ ^ 2 * Real.exp (-u * (σ - 3))) =
        ‖Gfun e d r u‖ ^ 2 * (Real.exp (-u) * Real.exp (2 * (-r * u)) * Real.exp (-u * (σ - 3))) := by
      ring
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, this, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  · intro u _
    have h := ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u))
    convert h.hasDerivWithinAt (s := Ioi 0) using 1 <;>
      first | with_reducible_and_instances rfl | rfl | simp [Function.comp_def]
  · intro u _ v _ h
    simpa using h

noncomputable def rate (e : Fin n → ℂ) (r δ : ℝ) (p q : Fin n × Fin J) : ℂ :=
  wexp e r p + conj (wexp e r q) + (δ : ℂ)

def tdeg (p q : Fin n × Fin J) : ℕ := (p.2 : ℕ) + (q.2 : ℕ)

noncomputable def crossFun (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r δ : ℝ) (p q : Fin n × Fin J)
    (u : ℝ) : ℂ :=
  (bcoef d p * conj (bcoef d q)) * ((u : ℂ) ^ tdeg p q * Complex.exp (-rate e r δ p q * u))

noncomputable def crossVal (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r δ : ℝ) (p q : Fin n × Fin J) : ℂ :=
  (bcoef d p * conj (bcoef d q)) * (((tdeg p q).factorial : ℂ) / rate e r δ p q ^ (tdeg p q + 1))

noncomputable def Ssum (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r δ : ℝ) : ℂ :=
  ∑ p ∈ supp d, ∑ q ∈ supp d, crossVal e d r δ p q

lemma rate_re (e : Fin n → ℂ) (r δ : ℝ) (p q : Fin n × Fin J) :
    (rate e r δ p q).re = (wexp e r p).re + (wexp e r q).re + δ := by
  simp [rate]

lemma rate_im (e : Fin n → ℂ) (r δ : ℝ) (p q : Fin n × Fin J) :
    (rate e r δ p q).im = (wexp e r p).im - (wexp e r q).im := by
  simp [rate]; ring

lemma normSq_G_mul_exp (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r δ u : ℝ) :
    ‖Gfun e d r u‖ ^ 2 * Real.exp (-δ * u) =
      (∑ p ∈ supp d, ∑ q ∈ supp d, crossFun e d r δ p q u).re := by
  have hG : (‖Gfun e d r u‖ ^ 2 : ℝ) = (Gfun e d r u * conj (Gfun e d r u)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hprod : Gfun e d r u * conj (Gfun e d r u) * ((Real.exp (-δ * u) : ℝ) : ℂ) =
      ∑ p ∈ supp d, ∑ q ∈ supp d, crossFun e d r δ p q u := by
    unfold Gfun
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold crossFun rate tdeg
    simp only [map_mul, map_pow, Complex.conj_ofReal, ← Complex.exp_conj, map_neg]
    have hexp : Complex.exp (-(wexp e r p + conj (wexp e r q) + (δ : ℂ)) * u) =
        Complex.exp (-(u : ℂ) * wexp e r p) * Complex.exp (-(u : ℂ) * conj (wexp e r q)) *
          Complex.exp (-(δ : ℂ) * u) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    rw [hexp, pow_add, Complex.ofReal_exp]
    push_cast
    ring
  rw [← hprod, hG]
  rw [mul_comm (Gfun e d r u * conj (Gfun e d r u)) _, Complex.re_ofReal_mul]
  ring

lemma rate_re_pos (e : Fin n → ℂ) (r δ : ℝ) (hδ : 0 < δ) (p q : Fin n × Fin J)
    (hp : 0 ≤ (wexp e r p).re) (hq : 0 ≤ (wexp e r q).re) : 0 < (rate e r δ p q).re := by
  rw [rate_re]; linarith

lemma integrableOn_crossFun (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r δ : ℝ) (hδ : 0 < δ)
    (p q : Fin n × Fin J) (hp : 0 ≤ (wexp e r p).re) (hq : 0 ≤ (wexp e r q).re) :
    IntegrableOn (crossFun e d r δ p q) (Ioi 0) := by
  unfold crossFun
  exact (integrableOn_pow_mul_exp _ (rate_re_pos e r δ hδ p q hp hq) _).const_mul _

lemma integral_crossFun (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r δ : ℝ) (hδ : 0 < δ)
    (p q : Fin n × Fin J) (hp : 0 ≤ (wexp e r p).re) (hq : 0 ≤ (wexp e r q).re) :
    ∫ u in Ioi (0 : ℝ), crossFun e d r δ p q u = crossVal e d r δ p q := by
  unfold crossFun crossVal
  rw [integral_const_mul, integral_pow_mul_exp _ (rate_re_pos e r δ hδ p q hp hq)]

lemma lintegral_G_eq (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r δ : ℝ) (hδ : 0 < δ)
    (hw : ∀ p ∈ supp d, 0 ≤ (wexp e r p).re) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (‖Gfun e d r u‖ ^ 2 * Real.exp (-δ * u)) =
      ENNReal.ofReal ((Ssum e d r δ).re) := by
  have hint : IntegrableOn (fun u : ℝ => ∑ p ∈ supp d, ∑ q ∈ supp d, crossFun e d r δ p q u) (Ioi 0) := by
    refine integrable_finsetSum _ fun p hp => integrable_finsetSum _ fun q hq => ?_
    exact integrableOn_crossFun e d r δ hδ p q (hw p hp) (hw q hq)
  have hint' : IntegrableOn (fun u : ℝ => ‖Gfun e d r u‖ ^ 2 * Real.exp (-δ * u)) (Ioi 0) := by
    have := hint.re
    refine this.congr (ae_of_all _ fun u => ?_)
    simp only [RCLike.re_to_complex]
    rw [normSq_G_mul_exp]
  rw [← ofReal_integral_eq_lintegral_ofReal hint' (ae_of_all _ fun u => by positivity)]
  congr 1
  have h1 : ∫ u in Ioi (0 : ℝ), ‖Gfun e d r u‖ ^ 2 * Real.exp (-δ * u) =
      ∫ u in Ioi (0 : ℝ), RCLike.re (∑ p ∈ supp d, ∑ q ∈ supp d, crossFun e d r δ p q u) := by
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [RCLike.re_to_complex]
    rw [normSq_G_mul_exp]
  rw [h1, integral_re hint, RCLike.re_to_complex]
  congr 1
  unfold Ssum
  rw [integral_finsetSum _ (fun p hp => integrable_finsetSum _ fun q hq =>
    integrableOn_crossFun e d r δ hδ p q (hw p hp) (hw q hq))]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_finsetSum _ (fun q hq => integrableOn_crossFun e d r δ hδ p q (hw p hp) (hw q hq))]
  refine Finset.sum_congr rfl fun q hq => ?_
  exact integral_crossFun e d r δ hδ p q (hw p hp) (hw q hq)

noncomputable def topSet (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r : ℝ) (jstar : ℕ) :
    Finset (Fin n × Fin J) :=
  (supp d).filter fun p => (wexp e r p).re = 0 ∧ (p.2 : ℕ) = jstar

noncomputable def Kb (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r : ℝ) (p q : Fin n × Fin J) : ℝ :=
  ‖bcoef d p‖ * ‖bcoef d q‖ * (tdeg p q).factorial *
    (if 0 < (wexp e r p).re + (wexp e r q).re then
        1 / ((wexp e r p).re + (wexp e r q).re) ^ (tdeg p q + 1)
      else if p.1 ≠ q.1 then 1 / |(wexp e r p).im - (wexp e r q).im| ^ (tdeg p q + 1)
      else 1)

lemma Kb_nonneg (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r : ℝ) (p q : Fin n × Fin J) :
    0 ≤ Kb e d r p q := by
  unfold Kb
  refine mul_nonneg (by positivity) ?_
  split_ifs <;> positivity

noncomputable def diagBonus (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r : ℝ) (jstar : ℕ) (δ : ℝ)
    (p q : Fin n × Fin J) : ℝ :=
  if p = q then (if p ∈ topSet e d r jstar then
    ‖bcoef d p‖ ^ 2 * (2 * jstar).factorial / δ ^ (2 * jstar + 1) else 0) else 0

lemma norm_crossVal (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r δ : ℝ) (p q : Fin n × Fin J) :
    ‖crossVal e d r δ p q‖ =
      ‖bcoef d p‖ * ‖bcoef d q‖ * ((tdeg p q).factorial / ‖rate e r δ p q‖ ^ (tdeg p q + 1)) := by
  unfold crossVal
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_div, norm_pow, Complex.norm_natCast]

lemma re_ge_neg_norm (z : ℂ) : -‖z‖ ≤ z.re := by
  have := Complex.abs_re_le_norm z
  rw [abs_le] at this
  exact this.1

lemma bcoef_ne_zero_of_mem_supp {d : Fin n → Fin J → ℂ} {p : Fin n × Fin J} (hp : p ∈ supp d) :
    bcoef d p ≠ 0 := by
  rw [mem_supp] at hp
  unfold bcoef
  exact mul_ne_zero hp (pow_ne_zero _ (by norm_num))

lemma crossVal_re_ge (e : Fin n → ℂ) (he : Function.Injective e) (d : Fin n → Fin J → ℂ) (r : ℝ)
    (jstar : ℕ) (hw : ∀ p ∈ supp d, 0 ≤ (wexp e r p).re)
    (hj : ∀ p ∈ supp d, (wexp e r p).re = 0 → (p.2 : ℕ) ≤ jstar)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (p q : Fin n × Fin J) (hp : p ∈ supp d) (hq : q ∈ supp d) :
    diagBonus e d r jstar δ p q - Kb e d r p q / δ ^ (2 * jstar) ≤ (crossVal e d r δ p q).re := by
  have hKnn := Kb_nonneg e d r p q
  have hδpow_le_one : δ ^ (2 * jstar) ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hδpow_pos : 0 < δ ^ (2 * jstar) := pow_pos hδ _

  have tool : diagBonus e d r jstar δ p q = 0 → ‖crossVal e d r δ p q‖ ≤ Kb e d r p q →
      diagBonus e d r jstar δ p q - Kb e d r p q / δ ^ (2 * jstar) ≤ (crossVal e d r δ p q).re := by
    intro h0 hle
    rw [h0, zero_sub]
    have h1 : Kb e d r p q ≤ Kb e d r p q / δ ^ (2 * jstar) := by
      rw [le_div_iff₀ hδpow_pos]
      exact mul_le_of_le_one_right hKnn hδpow_le_one
    have h2 := re_ge_neg_norm (crossVal e d r δ p q)
    linarith
  by_cases hpos : 0 < (wexp e r p).re + (wexp e r q).re
  ·
    have hbonus : diagBonus e d r jstar δ p q = 0 := by
      unfold diagBonus
      split_ifs with h1 h2
      · exfalso
        subst h1
        have : (wexp e r p).re = 0 := ((Finset.mem_filter.mp h2).2).1
        linarith
      · rfl
      · rfl
    apply tool hbonus
    rw [norm_crossVal]
    unfold Kb
    rw [if_pos hpos, mul_assoc (‖bcoef d p‖ * ‖bcoef d q‖)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hre : (wexp e r p).re + (wexp e r q).re ≤ ‖rate e r δ p q‖ := by
      have := Complex.re_le_norm (rate e r δ p q)
      rw [rate_re] at this
      linarith
    exact one_div_le_one_div_of_le (pow_pos hpos _) (pow_le_pow_left₀ hpos.le hre _)
  ·
    have hp0 : (wexp e r p).re = 0 := by have := hw p hp; have := hw q hq; linarith
    have hq0 : (wexp e r q).re = 0 := by have := hw p hp; have := hw q hq; linarith
    by_cases hne : p.1 ≠ q.1
    ·
      have him : (wexp e r p).im ≠ (wexp e r q).im := by
        intro h
        apply hne
        apply he
        apply Complex.ext
        · have h1 : (wexp e r p).re = (wexp e r q).re := by rw [hp0, hq0]
          simpa [wexp] using h1
        · simpa [wexp] using h
      have hlam : 0 < |(wexp e r p).im - (wexp e r q).im| := abs_pos.mpr (sub_ne_zero.mpr him)
      have hbonus : diagBonus e d r jstar δ p q = 0 := by
        unfold diagBonus
        rw [if_neg]
        intro h; exact hne (by rw [h])
      apply tool hbonus
      rw [norm_crossVal]
      unfold Kb
      rw [if_neg hpos, if_pos hne, mul_assoc (‖bcoef d p‖ * ‖bcoef d q‖)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have him_le : |(wexp e r p).im - (wexp e r q).im| ≤ ‖rate e r δ p q‖ := by
        have := Complex.abs_im_le_norm (rate e r δ p q)
        rw [rate_im] at this
        exact this
      exact one_div_le_one_div_of_le (pow_pos hlam _) (pow_le_pow_left₀ hlam.le him_le _)
    ·
      push Not at hne
      have hweq : wexp e r p = wexp e r q := by simp [wexp, hne]
      have hrate : rate e r δ p q = (δ : ℂ) := by
        unfold rate
        rw [← hweq]
        apply Complex.ext
        · simp [hp0]
        · simp
      by_cases hjj : (p.2 : ℕ) = jstar ∧ (q.2 : ℕ) = jstar
      ·
        have hpq : p = q := Prod.ext hne (Fin.ext (by rw [hjj.1, hjj.2]))
        subst hpq
        have hmem : p ∈ topSet e d r jstar := Finset.mem_filter.mpr ⟨hp, hp0, hjj.1⟩
        have hbonus : diagBonus e d r jstar δ p p =
            ‖bcoef d p‖ ^ 2 * (2 * jstar).factorial / δ ^ (2 * jstar + 1) := by
          unfold diagBonus
          rw [if_pos rfl, if_pos hmem]
        have hval : crossVal e d r δ p p =
            ((‖bcoef d p‖ ^ 2 * (2 * jstar).factorial / δ ^ (2 * jstar + 1) : ℝ) : ℂ) := by
          unfold crossVal
          rw [hrate, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          have htd : tdeg p p = 2 * jstar := by unfold tdeg; rw [hjj.1]; ring
          rw [htd]
          push_cast
          ring
        rw [hbonus, hval, Complex.ofReal_re]
        have : 0 ≤ Kb e d r p p / δ ^ (2 * jstar) := by positivity
        linarith
      ·
        have hle : tdeg p q + 1 ≤ 2 * jstar := by
          have h1 := hj p hp hp0
          have h2 := hj q hq hq0
          unfold tdeg
          rcases Nat.lt_or_ge (p.2 : ℕ) jstar with h | h
          · omega
          · have : (p.2 : ℕ) = jstar := le_antisymm h1 h
            have : (q.2 : ℕ) ≠ jstar := fun h' => hjj ⟨this, h'⟩
            omega
        have hbonus : diagBonus e d r jstar δ p q = 0 := by
          unfold diagBonus
          split_ifs with h1 h2
          · exfalso
            subst h1
            exact hjj ⟨((Finset.mem_filter.mp h2).2).2, ((Finset.mem_filter.mp h2).2).2⟩
          · rfl
          · rfl
        rw [hbonus, zero_sub]
        have h2 := re_ge_neg_norm (crossVal e d r δ p q)
        have h3 : ‖crossVal e d r δ p q‖ ≤ Kb e d r p q / δ ^ (2 * jstar) := by
          rw [norm_crossVal]
          unfold Kb
          rw [if_neg hpos, if_neg (not_not.mpr hne), mul_one, hrate, Complex.norm_real,
            Real.norm_of_nonneg hδ.le]
          rw [mul_div_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine div_le_div_of_nonneg_left (by positivity) hδpow_pos ?_
          exact pow_le_pow_of_le_one hδ.le hδ1 hle
        linarith

lemma Ssum_re_ge (e : Fin n → ℂ) (he : Function.Injective e) (d : Fin n → Fin J → ℂ) (r : ℝ)
    (jstar : ℕ) (hw : ∀ p ∈ supp d, 0 ≤ (wexp e r p).re)
    (hj : ∀ p ∈ supp d, (wexp e r p).re = 0 → (p.2 : ℕ) ≤ jstar)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ p ∈ topSet e d r jstar, ‖bcoef d p‖ ^ 2) * (2 * jstar).factorial / δ ^ (2 * jstar + 1) -
        (∑ p ∈ supp d, ∑ q ∈ supp d, Kb e d r p q) / δ ^ (2 * jstar) ≤ (Ssum e d r δ).re := by
  unfold Ssum
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  have hmain : ∑ p ∈ supp d, ∑ q ∈ supp d,
      (diagBonus e d r jstar δ p q - Kb e d r p q / δ ^ (2 * jstar)) ≤
      ∑ p ∈ supp d, ∑ q ∈ supp d, (crossVal e d r δ p q).re := by
    refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
    exact crossVal_re_ge e he d r jstar hw hj δ hδ hδ1 p q hp hq
  refine le_trans (le_of_eq ?_) hmain
  simp_rw [Finset.sum_sub_distrib]
  rw [Finset.sum_div]
  simp_rw [Finset.sum_div]
  congr 1

  have hinner : ∀ p ∈ supp d, ∑ q ∈ supp d, diagBonus e d r jstar δ p q =
      if p ∈ topSet e d r jstar then ‖bcoef d p‖ ^ 2 * (2 * jstar).factorial / δ ^ (2 * jstar + 1)
        else 0 := by
    intro p hp
    unfold diagBonus
    rw [Finset.sum_ite_eq]
    rw [if_pos hp]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_mul, Finset.sum_div]
  have hfilt : (supp d).filter (fun p => p ∈ topSet e d r jstar) = topSet e d r jstar := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right]
    exact Finset.filter_subset _ _
  rw [hfilt]

lemma Ssum_re_lower (e : Fin n → ℂ) (he : Function.Injective e) (d : Fin n → Fin J → ℂ) (r : ℝ)
    (jstar : ℕ) (hw : ∀ p ∈ supp d, 0 ≤ (wexp e r p).re)
    (hj : ∀ p ∈ supp d, (wexp e r p).re = 0 → (p.2 : ℕ) ≤ jstar)
    (htop : (topSet e d r jstar).Nonempty) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      κ / δ ^ (2 * jstar + 1) ≤ (Ssum e d r δ).re := by
  set B : ℝ := ∑ p ∈ topSet e d r jstar, ‖bcoef d p‖ ^ 2 with hB
  set Ktot : ℝ := ∑ p ∈ supp d, ∑ q ∈ supp d, Kb e d r p q with hKtot
  have hBpos : 0 < B := by
    obtain ⟨p₀, hp₀⟩ := htop
    have hp₀s : p₀ ∈ supp d := (Finset.mem_filter.mp hp₀).1
    have h1 : 0 < ‖bcoef d p₀‖ ^ 2 := by
      have := bcoef_ne_zero_of_mem_supp hp₀s
      positivity
    have h2 : ‖bcoef d p₀‖ ^ 2 ≤ B :=
      Finset.single_le_sum (f := fun p => ‖bcoef d p‖ ^ 2) (fun _ _ => by positivity) hp₀
    linarith
  have hKnn : 0 ≤ Ktot :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => Kb_nonneg e d r p q
  set A : ℝ := B * (2 * jstar).factorial with hA
  have hApos : 0 < A := by positivity
  refine ⟨A / 2, by positivity, min 1 (A / (2 * (Ktot + 1))), ?_, min_le_left _ _, ?_⟩
  · refine lt_min one_pos ?_
    positivity
  intro δ hδ hδle
  have hδ1 : δ ≤ 1 := le_trans hδle (min_le_left _ _)
  have hδ2 : δ ≤ A / (2 * (Ktot + 1)) := le_trans hδle (min_le_right _ _)
  have hmain := Ssum_re_ge e he d r jstar hw hj δ hδ hδ1
  rw [← hB, ← hKtot] at hmain
  have hpow : 0 < δ ^ (2 * jstar + 1) := pow_pos hδ _
  have hpow' : 0 < δ ^ (2 * jstar) := pow_pos hδ _

  have hK : Ktot / δ ^ (2 * jstar) ≤ (A / 2) / δ ^ (2 * jstar + 1) := by
    rw [div_le_div_iff₀ hpow' hpow, pow_succ]
    have h1 : Ktot * δ ≤ A / 2 := by
      have : Ktot * δ ≤ (Ktot + 1) * δ := by nlinarith
      have h3 : (Ktot + 1) * δ ≤ (Ktot + 1) * (A / (2 * (Ktot + 1))) :=
        mul_le_mul_of_nonneg_left hδ2 (by positivity)
      have h4 : (Ktot + 1) * (A / (2 * (Ktot + 1))) = A / 2 := by
        field_simp
      linarith
    calc Ktot * (δ ^ (2 * jstar) * δ) = (Ktot * δ) * δ ^ (2 * jstar) := by ring
      _ ≤ (A / 2) * δ ^ (2 * jstar) := mul_le_mul_of_nonneg_right h1 hpow'.le
  have hEq : A / δ ^ (2 * jstar + 1) - (A / 2) / δ ^ (2 * jstar + 1) = (A / 2) / δ ^ (2 * jstar + 1) := by
    field_simp
    ring
  have : B * (2 * jstar).factorial / δ ^ (2 * jstar + 1) = A / δ ^ (2 * jstar + 1) := by rw [hA]
  linarith

noncomputable def Lms (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ y in Ioc (0 : ℝ) 1, (‖mfun e d y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (y ^ (σ - 3))

lemma Lms_eq (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r σ : ℝ) :
    Lms e d σ = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (‖Gfun e d r u‖ ^ 2 * Real.exp (-(σ - 2 + 2 * r) * u)) :=
  lintegral_change e d r σ

lemma lintegral_G_mono (e : Fin n → ℂ) (d : Fin n → Fin J → ℂ) (r : ℝ) {δ δ' : ℝ} (h : δ' ≤ δ) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (‖Gfun e d r u‖ ^ 2 * Real.exp (-δ * u)) ≤
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (‖Gfun e d r u‖ ^ 2 * Real.exp (-δ' * u)) := by
  refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [Real.exp_le_exp]
  have : 0 ≤ u := le_of_lt hu
  nlinarith

theorem main (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e) (d : Fin n → Fin J → ℂ)
    (hM : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∃ σ : ℝ, 1 < σ ∧ σ < 1 + ε ∧
      ENNReal.ofReal (σ - 1) * Lms e d σ ≤ ENNReal.ofReal C) :
    ∀ (i : Fin n) (j : Fin J), ((e i).re < 1 / 2 ∨ ((e i).re = 1 / 2 ∧ 1 ≤ (j : ℕ))) → d i j = 0 := by
  intro i₁ j₁ hij
  by_contra hne
  obtain ⟨C, hC⟩ := hM

  set I : Finset (Fin n × Fin J) := supp d with hI
  have hp₁ : (i₁, j₁) ∈ I := mem_supp.mpr hne
  have hIne : I.Nonempty := ⟨_, hp₁⟩
  set r : ℝ := (I.image fun p => (e p.1).re).min' (hIne.image _) with hr_def
  have hr_le : ∀ p ∈ I, r ≤ (e p.1).re := fun p hp =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem (fun p : Fin n × Fin J => (e p.1).re) hp)
  have hr_mem : ∃ p ∈ I, (e p.1).re = r := by
    have := Finset.min'_mem (I.image fun p => (e p.1).re) (hIne.image _)
    obtain ⟨p, hp, hpr⟩ := Finset.mem_image.mp this
    exact ⟨p, hp, hpr⟩
  have hw : ∀ p ∈ I, 0 ≤ (wexp e r p).re := by
    intro p hp
    have := hr_le p hp
    simp only [wexp, Complex.sub_re, Complex.ofReal_re]
    linarith
  have hwre : ∀ p : Fin n × Fin J, (wexp e r p).re = (e p.1).re - r := by
    intro p; simp [wexp]
  have hr_half : r ≤ 1 / 2 := by
    have := hr_le _ hp₁
    rcases hij with h | ⟨h, _⟩
    · simp only at this; linarith
    · simp only at this; linarith

  set T : Finset (Fin n × Fin J) := I.filter fun p => (e p.1).re = r with hT
  have hTne : T.Nonempty := by
    obtain ⟨p, hp, hpr⟩ := hr_mem
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpr⟩⟩
  set jstar : ℕ := (T.image fun p => (p.2 : ℕ)).max' (hTne.image _) with hjstar_def
  have hj : ∀ p ∈ I, (wexp e r p).re = 0 → (p.2 : ℕ) ≤ jstar := by
    intro p hp hp0
    have hpT : p ∈ T := Finset.mem_filter.mpr ⟨hp, by rw [hwre] at hp0; linarith⟩
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem (fun p : Fin n × Fin J => (p.2 : ℕ)) hpT)
  have htop : (topSet e d r jstar).Nonempty := by
    have := Finset.max'_mem (T.image fun p => (p.2 : ℕ)) (hTne.image _)
    obtain ⟨p, hpT, hpj⟩ := Finset.mem_image.mp this
    have hpI : p ∈ I := (Finset.mem_filter.mp hpT).1
    have hpr : (e p.1).re = r := (Finset.mem_filter.mp hpT).2
    refine ⟨p, Finset.mem_filter.mpr ⟨hpI, ?_, hpj⟩⟩
    rw [hwre, hpr, sub_self]

  obtain ⟨κ, hκ, δ₁, hδ₁, hδ₁1, hlow⟩ := Ssum_re_lower e he d r jstar hw hj htop

  have hΛ : ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ENNReal.ofReal (κ / δ ^ (2 * jstar + 1)) ≤
        ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (‖Gfun e d r u‖ ^ 2 * Real.exp (-δ * u)) := by
    intro δ hδ hδle
    rw [lintegral_G_eq e d r δ hδ hw]
    exact ENNReal.ofReal_le_ofReal (hlow δ hδ hδle)
  rcases lt_or_eq_of_le hr_half with hr | hr
  ·
    obtain ⟨σ₀, hσ₀1, hσ₀2, hbound⟩ := hC (1 - 2 * r) (by linarith)
    have hLfin : Lms e d σ₀ ≠ ⊤ := by
      intro htop'
      rw [htop', ENNReal.mul_top (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith)] at hbound
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hbound)
    set Lr : ℝ := (Lms e d σ₀).toReal with hLr
    have hLr0 : 0 ≤ Lr := ENNReal.toReal_nonneg
    have hdom : ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → κ / δ ^ (2 * jstar + 1) ≤ Lr := by
      intro δ hδ hδle
      have h1 := hΛ δ hδ hδle
      have h2 : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (‖Gfun e d r u‖ ^ 2 * Real.exp (-δ * u)) ≤
          Lms e d σ₀ := by
        rw [Lms_eq e d r σ₀]
        exact lintegral_G_mono e d r (by linarith)
      exact (ENNReal.ofReal_le_iff_le_toReal hLfin).mp (h1.trans h2)
    set δ : ℝ := min δ₁ (κ / (Lr + 1)) with hδ_def
    have hδpos : 0 < δ := lt_min hδ₁ (by positivity)
    have hδle : δ ≤ δ₁ := min_le_left _ _
    have hδle' : δ ≤ κ / (Lr + 1) := min_le_right _ _
    have hδ1 : δ ≤ 1 := hδle.trans hδ₁1
    have h1 := hdom δ hδpos hδle
    have h2 : κ / δ ≤ κ / δ ^ (2 * jstar + 1) := by
      refine div_le_div_of_nonneg_left hκ.le (pow_pos hδpos _) ?_
      calc δ ^ (2 * jstar + 1) ≤ δ ^ 1 := pow_le_pow_of_le_one hδpos.le hδ1 (by omega)
        _ = δ := pow_one δ
    have h3 : Lr + 1 ≤ κ / δ := by
      rw [le_div_iff₀ hδpos]
      calc (Lr + 1) * δ ≤ (Lr + 1) * (κ / (Lr + 1)) := mul_le_mul_of_nonneg_left hδle' (by positivity)
        _ = κ := by field_simp
    linarith
  ·
    have hjstar : 1 ≤ jstar := by
      rcases hij with h | ⟨h, hj1⟩
      · exfalso
        have := hr_le _ hp₁
        simp only at this
        linarith
      · have h0 : (wexp e r (i₁, j₁)).re = 0 := by rw [hwre]; simp only; rw [h, hr]; ring
        exact hj1.trans (hj _ hp₁ h0)
    set ε : ℝ := min δ₁ (κ / (|C| + 1)) with hε_def
    have hε : 0 < ε := lt_min hδ₁ (by positivity)
    obtain ⟨σ, hσ1, hσ2, hbound⟩ := hC ε hε
    have hδpos : 0 < σ - 1 := by linarith
    have hδlt : σ - 1 < ε := by linarith
    have hδle : σ - 1 ≤ δ₁ := hδlt.le.trans (min_le_left _ _)
    have hδ1 : σ - 1 ≤ 1 := hδle.trans hδ₁1
    rw [Lms_eq e d r σ, show σ - 2 + 2 * r = σ - 1 by rw [hr]; ring,
      lintegral_G_eq e d r (σ - 1) hδpos hw, ← ENNReal.ofReal_mul hδpos.le] at hbound
    have hX : |C| + 1 ≤ (σ - 1) * (Ssum e d r (σ - 1)).re := by
      have h1 := hlow (σ - 1) hδpos hδle
      have h2 : (σ - 1) * (κ / (σ - 1) ^ (2 * jstar + 1)) = κ / (σ - 1) ^ (2 * jstar) := by
        rw [pow_succ]
        field_simp
      have h3 : κ / (σ - 1) ≤ κ / (σ - 1) ^ (2 * jstar) := by
        refine div_le_div_of_nonneg_left hκ.le (pow_pos hδpos _) ?_
        calc (σ - 1) ^ (2 * jstar) ≤ (σ - 1) ^ 1 := pow_le_pow_of_le_one hδpos.le hδ1 (by omega)
          _ = σ - 1 := pow_one _
      have h4 : |C| + 1 ≤ κ / (σ - 1) := by
        have h5 : κ / ε ≤ κ / (σ - 1) := div_le_div_of_nonneg_left hκ.le hδpos hδlt.le
        have h6 : |C| + 1 ≤ κ / ε := by
          rw [le_div_iff₀ hε]
          calc (|C| + 1) * ε ≤ (|C| + 1) * (κ / (|C| + 1)) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
            _ = κ := by field_simp
        linarith
      have h7 : (σ - 1) * (κ / (σ - 1) ^ (2 * jstar + 1)) ≤ (σ - 1) * (Ssum e d r (σ - 1)).re :=
        mul_le_mul_of_nonneg_left h1 hδpos.le
      linarith
    rcases ENNReal.ofReal_le_ofReal_iff'.mp hbound with h | h
    · have := le_abs_self C
      linarith
    · have := abs_nonneg C
      linarith

end KcMeanSquare

theorem solution
    (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e) (d : Fin n → Fin J → ℂ)
    (hM : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∃ σ : ℝ, 1 < σ ∧ σ < 1 + ε ∧
      ENNReal.ofReal (σ - 1) *
          ∫⁻ y in Set.Ioc (0 : ℝ) 1,
            (‖∑ i : Fin n, ∑ j : Fin J, d i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖₊ : ℝ≥0∞) ^ 2 *
              ENNReal.ofReal (y ^ (σ - 3)) ∂volume ≤
        ENNReal.ofReal C) :
    ∀ (i : Fin n) (j : Fin J), ((e i).re < 1 / 2 ∨ ((e i).re = 1 / 2 ∧ 1 ≤ (j : ℕ))) → d i j = 0 :=
  KcMeanSquare.main n J e he d hM

end S_MeanSquare_eq_zero_of_re_lt_one_half_or_log_of_liminf_sub_one_mul_lintegral_cpow_log_sq_le
end P2MW
export P2MW.S_MeanSquare_eq_zero_of_re_lt_one_half_or_log_of_liminf_sub_one_mul_lintegral_cpow_log_sq_le (solution)
