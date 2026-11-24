-- Prove2me | solution 1 for HermitekLEAN.finite_modulus_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:27.972415+00:00
-- url     : https://prove2.me/submissions/e033e9bf-73c8-488d-8851-c3367d2c1026

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ModulusRigidity
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_circle
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_eventually_nonzero
public import Theorems.Thm_HermitekLEAN_qkn_ratio_control
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped Topology
noncomputable section
namespace HermitekLEAN
private lemma circleLeadingFactor_ne_zero (k : ℕ) {r : ℝ} (hr : 0 < r) :
    circleLeadingFactor k r ≠ 0 := by
  have hpos : 0 < ((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) := by positivity
  simpa [circleLeadingFactor] using hpos.ne'
private lemma norm_circleLeadingFactor_mul_cancel
    {k : ℕ} {r : ℝ} (hr : 0 < r) {f x y : ℂ} (hf : ‖f‖ = 1)
    (h : ‖circleLeadingFactor k r * f * x‖ = ‖circleLeadingFactor k r * f * y‖) :
    ‖x‖ = ‖y‖ := by
  simp only [norm_mul, hf, mul_one] at h
  exact mul_left_cancel₀ (norm_ne_zero_iff.mpr (circleLeadingFactor_ne_zero k hr)) h
private lemma integrable_circle_of_continuous {φ : Circle → ℂ} (hφ : Continuous φ) :
    Integrable φ AddCircle.haarAddCircle :=
  hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)
private theorem qkn_ratio_tendsto_zero {k i d : ℕ} (hi : i < d) :
    Filter.Tendsto (fun r : ℝ => ((qkn k i r : ℂ) / (qkn k d r : ℂ))) Filter.atTop (𝓝 (0 : ℂ)) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨C, R0, hC, hR0, hbound⟩ := qkn_ratio_control (k := k) (n := i) (d := d) hi
  have hC0 : Filter.Tendsto (fun r : ℝ => (C : ℝ) / r) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (C : ℝ)
  have hbound' : ∀ᶠ r in Filter.atTop, ‖((qkn k i r : ℂ) / (qkn k d r : ℂ))‖ ≤ C / r := by
    filter_upwards [Filter.eventually_ge_atTop R0] with r hr
    exact hbound r hr
  have hnonneg : ∀ᶠ r in Filter.atTop, 0 ≤ ‖((qkn k i r : ℂ) / (qkn k d r : ℂ))‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  exact squeeze_zero' hnonneg hbound' hC0
private theorem qkn_ratio_prod_tendsto_zero {k i j p q : ℕ} (hij : i < j) (hpq : p < q) :
    Filter.Tendsto
      (fun r : ℝ => ((qkn k i r : ℂ) / (qkn k j r : ℂ)) *
        ((qkn k p r : ℂ) / (qkn k q r : ℂ)))
      Filter.atTop (𝓝 (0 : ℂ)) := by
  simpa using (qkn_ratio_tendsto_zero (k := k) hij).mul (qkn_ratio_tendsto_zero (k := k) hpq)
private theorem pair_coeff_normalized_tendsto
    {k d : ℕ} (a : Fin (d + 1) → ℂ) (n : Fin (d + 1)) :
  Filter.Tendsto
      (fun r : ℝ =>
        ∑ p : Fin (d + 1) × Fin (d + 1),
          a p.1 * star (a p.2) *
            (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = (d : ℤ) - (n : ℤ) then 1 else 0) *
            ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
            ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ)))
      Filter.atTop (𝓝 (a ⟨d, Nat.lt_succ_self d⟩ * star (a n))) := by
  classical
  let topPair : Fin (d + 1) × Fin (d + 1) := (⟨d, Nat.lt_succ_self d⟩, n)
  let lim : Fin (d + 1) × Fin (d + 1) → ℂ :=
    fun p => if p = topPair then a ⟨d, Nat.lt_succ_self d⟩ * star (a n) else 0
  obtain ⟨Rd, hRd, hd_nonzero⟩ := qkn_eventually_nonzero k d
  obtain ⟨Rn, hRn, hn_nonzero⟩ := qkn_eventually_nonzero k n.1
  have hsum :
      Filter.Tendsto
        (fun r : ℝ =>
          ∑ p : Fin (d + 1) × Fin (d + 1),
            a p.1 * star (a p.2) *
              (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = (d : ℤ) - (n : ℤ) then 1 else 0) *
              ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ)))
        Filter.atTop (𝓝 (∑ p : Fin (d + 1) × Fin (d + 1), lim p)) := by
    refine tendsto_finsetSum
      (s := (Finset.univ : Finset (Fin (d + 1) × Fin (d + 1))))
      (f := fun p : Fin (d + 1) × Fin (d + 1) => fun r : ℝ =>
        a p.1 * star (a p.2) *
          (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = (d : ℤ) - (n : ℤ) then 1 else 0) *
          ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
          ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ)))
      (a := lim) ?_
    intro p hp
    by_cases htop : p = topPair
    · subst htop
      have hif :
          (if (d : ℤ) - (n.1 : ℤ) = (d : ℤ) - (n : ℤ) then (1 : ℂ) else 0) = 1 := by simp
      have hEq :
          (fun r : ℝ =>
            a ⟨d, Nat.lt_succ_self d⟩ * star (a n) *
              (if (d : ℤ) - (n.1 : ℤ) = (d : ℤ) - (n : ℤ) then 1 else 0) *
              ((qkn k d r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k n.1 r : ℂ) / (qkn k n.1 r : ℂ))) =ᶠ[Filter.atTop]
            fun _ => (lim topPair : ℂ) := by
        filter_upwards [Filter.eventually_ge_atTop Rd, Filter.eventually_ge_atTop Rn] with r hrD hrN
        have hd : (qkn k d r : ℂ) ≠ 0 := by exact_mod_cast hd_nonzero r hrD
        have hn : (qkn k n.1 r : ℂ) ≠ 0 := by exact_mod_cast hn_nonzero r hrN
        have hselfd : ((qkn k d r : ℂ) / (qkn k d r : ℂ)) = 1 := by field_simp [hd]
        have hselfn : ((qkn k n.1 r : ℂ) / (qkn k n.1 r : ℂ)) = 1 := by field_simp [hn]
        rw [hif, hselfd, hselfn]
        simp [topPair, lim]
      exact hEq.tendsto
    · by_cases hdiff : (p.1.1 : ℤ) - (p.2.1 : ℤ) = (d : ℤ) - (n : ℤ)
      · have hnot_d : p.1.1 ≠ d := by
          intro hdi
          have hj : p.2.1 = n.1 := by omega
          exact htop (by
            ext <;> simp [topPair, hdi, hj])
        have hnot_n : p.2.1 ≠ n.1 := by
          intro hjn
          simp_all
        have h1 : p.1.1 < d := lt_of_le_of_ne (Nat.le_of_lt_succ p.1.2) hnot_d
        have h2le : p.2.1 ≤ n.1 := by omega
        have h2 : p.2.1 < n.1 := lt_of_le_of_ne h2le hnot_n
        have hprod0 := qkn_ratio_prod_tendsto_zero (k := k) h1 h2
        simpa [topPair, lim, hdiff, htop, mul_assoc, mul_left_comm, mul_comm] using
          hprod0.const_mul (a p.1 * star (a p.2))
      · simp [lim, hdiff, htop]
  simpa [lim, topPair] using hsum
private theorem fourierCoeff_pair_expansion
    {D : ℕ} (c : Fin D → ℂ) (m : ℤ) :
    fourierCoeff (fun t : Circle =>
      ∑ p : Fin D × Fin D,
        c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) m =
      ∑ p : Fin D × Fin D,
        c p.1 * star (c p.2) * (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) := by
  classical
  have hsumfun :
      (∑ p : Fin D × Fin D,
        fun t : Circle => c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) =
      fun t : Circle => ∑ p : Fin D × Fin D,
        c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t := by
    ext t
    simp [Finset.sum_apply]
  have hsum := fourierCoeff.sum
    (s := (Finset.univ : Finset (Fin D × Fin D)))
    (f := fun p : Fin D × Fin D => fun t : Circle =>
      c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t)
    (by
      intro p hp
      refine integrable_circle_of_continuous ?_
      continuity)
  rw [hsumfun] at hsum
  have hsum' := congrArg (fun F => F m) hsum
  have hsum'' :
      fourierCoeff (fun t : Circle =>
        ∑ p : Fin D × Fin D,
          c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) m =
      ∑ p : Fin D × Fin D,
        fourierCoeff (fun t : Circle =>
          c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) m := by
    simpa only [Finset.sum_apply] using hsum'
  rw [hsum'']
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hfreq :
      fourierCoeff (T := T) (fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ))) m =
        if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0 := by
    have hpi :
        Pi.single (ι := ℤ) (M := fun _ => ℂ) ((p.1.1 : ℤ) - (p.2.1 : ℤ)) (1 : ℂ) m =
          if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0 := by
      rw [Pi.single_apply]
      simp [eq_comm]
    simpa using
      (congrArg (fun F : ℤ → ℂ => F m)
        (fourierCoeff_fourier (T := T) ((p.1.1 : ℤ) - (p.2.1 : ℤ)))).trans hpi
  calc
    fourierCoeff (fun t : Circle =>
      c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) m =
        c p.1 * star (c p.2) * fourierCoeff (T := T)
          (fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ))) m := by
            simpa [mul_assoc] using
              (fourierCoeff.const_mul (T := T)
                (f := fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)))
                (c := c p.1 * star (c p.2)) (n := m))
    _ = c p.1 * star (c p.2) * (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) := by rw [hfreq]
private theorem finiteCirclePoly_sum
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {r : ℝ} (_hr : 0 < r) (t : Circle) :
    finiteCirclePoly k r a t =
      ∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t := by
  rw [finiteCirclePoly,
    show positiveTrigonometricPolynomial (frequencyBand 0 (d + 1)) (finiteCircleCoeff k r a) t =
      ∑ n ∈ frequencyBand 0 (d + 1), finiteCircleCoeff k r a n * fourier (n : ℤ) t by rfl]
  have hband : frequencyBand 0 (d + 1) = Finset.range (d + 1) := by
    simpa [HermiteLEAN.frequencyBand] using
      (show Finset.Icc 0 d = Finset.range (d + 1) by
        ext n
        simp [Finset.mem_Icc])
  rw [hband, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxle : (x : ℕ) ≤ d := Nat.le_of_lt_succ x.is_lt
  simp [finiteCircleCoeff, fourier_apply, hxle]
private theorem finiteSeries_mul_star_expand {D : ℕ} (c : Fin D → ℂ) (t : Circle) :
    (∑ n : Fin D, c n * fourier (n : ℤ) t) *
        star (∑ n : Fin D, c n * fourier (n : ℤ) t) =
      ∑ p : Fin D × Fin D,
        c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t := by
  have hstar : star (∑ n : Fin D, c n * fourier (n : ℤ) t) =
      ∑ n : Fin D, star (c n * fourier (n : ℤ) t) := by simp
  have hconj : ∀ (x : Fin D) (t : Circle),
      (starRingEnd ℂ) ↑(AddCircle.toCircle ((x : ℕ) • t)) =
        ↑(AddCircle.toCircle (-((x : ℕ) • t))) := by
    intro x t
    rw [← Circle.coe_inv_eq_conj, ← AddCircle.toCircle_neg]
  rw [hstar, Fintype.sum_mul_sum]
  simp only [hconj, fourier_apply, natCast_zsmul, star_mul', RCLike.star_def, mul_assoc,
    mul_left_comm, mul_comm]
  rw [← Fintype.sum_prod_type']
  simp [mul_assoc, sub_eq_add_neg]
private theorem finiteCirclePoly_normSq_fourierCoeff
    {k d : ℕ} (c : Fin (d + 1) → ℂ) {r : ℝ} (hr : 0 < r) (m : ℤ) :
    fourierCoeff (fun t : Circle =>
      finiteCirclePoly k r c t * star (finiteCirclePoly k r c t)) m =
    ∑ p : Fin (d + 1) × Fin (d + 1),
      c p.1 * star (c p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        (qkn k p.1.1 r : ℂ) * (qkn k p.2.1 r : ℂ) := by
  have hprod_eq :
      (fun t : Circle => finiteCirclePoly k r c t * star (finiteCirclePoly k r c t)) =
      fun t : Circle =>
        ∑ p : Fin (d + 1) × Fin (d + 1),
          (c p.1 * (qkn k p.1.1 r : ℂ)) * star (c p.2 * (qkn k p.2.1 r : ℂ)) *
            fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t := by
    ext t
    rw [finiteCirclePoly_sum (k := k) (a := c) hr t]
    exact finiteSeries_mul_star_expand (fun i : Fin (d + 1) => c i * (qkn k i.1 r : ℂ)) t
  have hcoeff := congrArg (fun F : Circle → ℂ => fourierCoeff F m) hprod_eq
  simpa [mul_assoc, mul_left_comm, mul_comm, qkn_real] using
    (hcoeff.trans
      (fourierCoeff_pair_expansion (D := d + 1)
        (c := fun i : Fin (d + 1) => c i * (qkn k i.1 r : ℂ)) (m := m)))
private theorem pairSum_ratio_mul_den
    {k d : ℕ} (c : Fin (d + 1) → ℂ) (m : ℤ) {r : ℝ} (n1 : ℕ)
    (hd : (qkn k d r : ℂ) ≠ 0) (hn : (qkn k n1 r : ℂ) ≠ 0) :
    (∑ p : Fin (d + 1) × Fin (d + 1),
      c p.1 * star (c p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
        ((qkn k p.2.1 r : ℂ) / (qkn k n1 r : ℂ))) *
      ((qkn k d r : ℂ) * (qkn k n1 r : ℂ)) =
    ∑ p : Fin (d + 1) × Fin (d + 1),
      c p.1 * star (c p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        (qkn k p.1.1 r : ℂ) * (qkn k p.2.1 r : ℂ) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro p hp
  field_simp [hd, hn]
private lemma finite_modulus_coeff_rel {k d : ℕ} (a b : Fin (d + 1) → ℂ)
    (topA topB : ℂ) (htopA : topA = topCoeff a) (htopB : topB = topCoeff b)
    (_hprod_expand : ∀ {D : ℕ} (c : Fin D → ℂ) (t : Circle),
      (∑ n : Fin D, c n * fourier (n : ℤ) t) *
          star (∑ n : Fin D, c n * fourier (n : ℤ) t) =
        ∑ p : Fin D × Fin D,
          c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t)
    (_hsumA : ∀ {r : ℝ}, 0 < r → ∀ t : Circle,
      finiteCirclePoly k r a t =
        ∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t)
    (_hsumB : ∀ {r : ℝ}, 0 < r → ∀ t : Circle,
      finiteCirclePoly k r b t =
        ∑ i : Fin (d + 1), b i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t)
    (hpoly_norm : ∀ {r : ℝ}, 0 < r →
      ∀ t : Circle, ‖finiteCirclePoly k r b t‖ = ‖finiteCirclePoly k r a t‖) :
    ∀ n : Fin (d + 1), topA * star (a n) = topB * star (b n) := by
  intro n
  let m : ℤ := (d : ℤ) - (n : ℤ)
  let rawA : ℝ → ℂ := fun r =>
    ∑ p : Fin (d + 1) × Fin (d + 1),
      a p.1 * star (a p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        (qkn k p.1.1 r : ℂ) * (qkn k p.2.1 r : ℂ)
  let rawB : ℝ → ℂ := fun r =>
    ∑ p : Fin (d + 1) × Fin (d + 1),
      b p.1 * star (b p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        (qkn k p.1.1 r : ℂ) * (qkn k p.2.1 r : ℂ)
  let Fa : ℝ → ℂ := fun r =>
    ∑ p : Fin (d + 1) × Fin (d + 1),
      a p.1 * star (a p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
        ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ))
  let Fb : ℝ → ℂ := fun r =>
    ∑ p : Fin (d + 1) × Fin (d + 1),
      b p.1 * star (b p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
        ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ))
  have hAcoeff : ∀ r : ℝ, 0 < r →
      fourierCoeff (fun t : Circle =>
        finiteCirclePoly k r a t * star (finiteCirclePoly k r a t)) m = rawA r :=
    fun r hr => finiteCirclePoly_normSq_fourierCoeff (k := k) a hr m
  have hBcoeff : ∀ r : ℝ, 0 < r →
      fourierCoeff (fun t : Circle =>
        finiteCirclePoly k r b t * star (finiteCirclePoly k r b t)) m = rawB r :=
    fun r hr => finiteCirclePoly_normSq_fourierCoeff (k := k) b hr m
  have hraw_eq : ∀ r : ℝ, 0 < r → rawA r = rawB r := by
    intro r hr
    have hprod_eq :
        (fun t : Circle =>
          finiteCirclePoly k r a t * star (finiteCirclePoly k r a t)) =
        (fun t : Circle =>
          finiteCirclePoly k r b t * star (finiteCirclePoly k r b t)) := by
      ext t
      calc
        finiteCirclePoly k r a t * star (finiteCirclePoly k r a t) =
            ‖finiteCirclePoly k r a t‖ ^ 2 := by
              exact (RCLike.mul_conj (finiteCirclePoly k r a t))
        _ = ‖finiteCirclePoly k r b t‖ ^ 2 := by rw [hpoly_norm (r := r) hr t]
        _ = finiteCirclePoly k r b t * star (finiteCirclePoly k r b t) := by
              symm
              exact (RCLike.mul_conj (finiteCirclePoly k r b t))
    have hcoeff :=
      congrArg (fun F : Circle → ℂ => fourierCoeff F m) hprod_eq
    exact (hAcoeff r hr).symm.trans (hcoeff.trans (hBcoeff r hr))
  obtain ⟨Rd, hRd, hRd_nonzero⟩ := qkn_eventually_nonzero k d
  obtain ⟨Rn, hRn, hRn_nonzero⟩ := qkn_eventually_nonzero k n.1
  have hEqFaFb : Fa =ᶠ[Filter.atTop] Fb := by
    filter_upwards [Filter.eventually_ge_atTop (max Rd Rn)] with r hr
    have h1 : 1 ≤ r := by
      have hmax : 1 ≤ max Rd Rn := le_trans hRd (le_max_left _ _)
      exact le_trans hmax hr
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one h1
    have hraw := hraw_eq r hr_pos
    have hd : (qkn k d r : ℂ) ≠ 0 := by exact_mod_cast hRd_nonzero r (le_trans (le_max_left _ _) hr)
    have hn : (qkn k n.1 r : ℂ) ≠ 0 := by
      exact_mod_cast hRn_nonzero r (le_trans (le_max_right _ _) hr)
    have hmulA := pairSum_ratio_mul_den (k := k) a m n.1 hd hn
    have hmulB := pairSum_ratio_mul_den (k := k) b m n.1 hd hn
    have hD : ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) ≠ 0 := mul_ne_zero hd hn
    exact mul_right_cancel₀ hD (hmulA.trans (hraw.trans hmulB.symm))
  have hFa_tendsto : Filter.Tendsto Fa Filter.atTop (𝓝 (topA * star (a n))) := by
    rw [htopA]
    exact pair_coeff_normalized_tendsto (k := k) (d := d) (a := a) (n := n)
  have hFb_tendsto : Filter.Tendsto Fb Filter.atTop (𝓝 (topB * star (b n))) := by
    rw [htopB]
    exact pair_coeff_normalized_tendsto (k := k) (d := d) (a := b) (n := n)
  have hlim : topA * star (a n) = topB * star (b n) := by
    have hFa' : Filter.Tendsto Fb Filter.atTop (𝓝 (topA * star (a n))) :=
      hFa_tendsto.congr' hEqFaFb
    exact tendsto_nhds_unique hFa' hFb_tendsto
  exact hlim
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k d : ℕ}
      (a b : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0),
        (∀ z : ℂ, ‖finiteHermiteSum k b z‖ = ‖finiteHermiteSum k a z‖) →
          ∃ w : ℂ, ‖w‖ = 1 ∧ finiteHermiteSum k b = w • finiteHermiteSum k a := by
  intro k d a b hTop hmod
  let topA : ℂ := topCoeff a
  let topB : ℂ := topCoeff b
  let w : ℂ := topB / topA
  have htopA : topA ≠ 0 := hTop
  have hpoly_norm : ∀ {r : ℝ}, 0 < r →
      ∀ t : Circle, ‖finiteCirclePoly k r b t‖ = ‖finiteCirclePoly k r a t‖ := by
    intro r hr t
    have hB := finiteHermiteSum_circle (k := k) (a := b) (r := r) hr t
    have hA := finiteHermiteSum_circle (k := k) (a := a) (r := r) hr t
    have hnorm := hmod (circlePoint r t)
    rw [hB, hA] at hnorm
    exact norm_circleLeadingFactor_mul_cancel hr
      (by simp [fourier_apply, Circle.norm_coe]) hnorm
  have hcoeff_rel : ∀ n : Fin (d + 1), topA * star (a n) = topB * star (b n) :=
    finite_modulus_coeff_rel a b topA topB rfl rfl
      (fun c t => finiteSeries_mul_star_expand c t)
      (fun hr t => finiteCirclePoly_sum a hr t)
      (fun hr t => finiteCirclePoly_sum b hr t) hpoly_norm
  have htop_rel : topA * star topA = topB * star topB :=
    hcoeff_rel ⟨d, Nat.lt_succ_self d⟩
  have hw_norm : ‖w‖ = 1 := by
    dsimp [w]
    have hmul : ‖topA‖ * ‖topA‖ = ‖topB‖ * ‖topB‖ := by
      simpa [norm_mul, norm_star] using congrArg norm htop_rel
    have hsq : ‖topA‖ ^ 2 = ‖topB‖ ^ 2 := by simpa [sq] using hmul
    have hnorm : ‖topA‖ = ‖topB‖ := by
      rw [← Real.sqrt_sq (norm_nonneg topA), ← Real.sqrt_sq (norm_nonneg topB), hsq]
    have hb_norm : ‖topB‖ ≠ 0 := by
      have ha_norm : ‖topA‖ ≠ 0 := norm_ne_zero_iff.mpr htopA
      simpa [hnorm] using ha_norm
    simp_all
  have hw_conj : w * star w = 1 := by simpa [hw_norm] using (RCLike.mul_conj w)
  have hb_coeff : ∀ n : Fin (d + 1), b n = w * a n := by
    intro n
    have hrel := hcoeff_rel n
    have hw_top : topB = w * topA := by
      dsimp [w]
      field_simp [htopA]
    have hstarcoeff : star (a n) = w * star (b n) := by
      apply mul_left_cancel₀ htopA
      simpa [hw_top, mul_assoc, mul_left_comm, mul_comm] using hrel
    have hstarcoeff' : a n = star w * b n := by
      have h := congrArg star hstarcoeff
      simpa [star_mul, mul_assoc, mul_left_comm, mul_comm] using h
    rw [hstarcoeff', ← mul_assoc, hw_conj, one_mul]
  have hfun : finiteHermiteSum k b = w • finiteHermiteSum k a := by
    funext z
    calc
      finiteHermiteSum k b z = ∑ n : Fin (d + 1), w * (a n * Phi k n.1 z) := by
        simp [finiteHermiteSum, hb_coeff, mul_assoc, mul_left_comm, mul_comm]
      _ = w * ∑ n : Fin (d + 1), a n * Phi k n.1 z := by rw [Finset.mul_sum]
  refine ⟨w, hw_norm, hfun⟩
end HermitekLEAN
