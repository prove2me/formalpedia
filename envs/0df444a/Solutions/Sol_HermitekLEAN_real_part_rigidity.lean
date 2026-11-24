-- Prove2me | solution 1 for HermitekLEAN.real_part_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:27.060743+00:00
-- url     : https://prove2.me/submissions/48275118-966c-4991-8fe4-39bd46a2bdd9

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ModulusRigidity
public import Theorems.Thm_HermitekLEAN_circleSeries_fourierCoeff_hermiteCoeff
public import Theorems.Thm_HermitekLEAN_circleSeries_l2_identity_hermiteCoeff
public import Theorems.Thm_HermitekLEAN_circle_representation_hermiteCoeff
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_circle
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_mem_Hk
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_finiteHermiteSum
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_hermite_series_locally_uniform
public import Theorems.Thm_HermitekLEAN_qkn_eventually_nonzero
public import Theorems.Thm_HermitekLEAN_qkn_ratio_control
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_truncate_eq_finiteHermiteSum
public import Theorems.Thm_HermitekLEAN_truncate_unique
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
private theorem qkn_self_ratio_tendsto_one {k d : ℕ} :
    Filter.Tendsto (fun r : ℝ => ((qkn k d r : ℂ) / (qkn k d r : ℂ))) Filter.atTop (𝓝 (1 : ℂ)) := by
  obtain ⟨R0, hR0, hnonzero⟩ := qkn_eventually_nonzero k d
  have hEq :
      (fun r : ℝ => ((qkn k d r : ℂ) / (qkn k d r : ℂ))) =ᶠ[Filter.atTop] fun _ => (1 : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop R0] with r hr
    simp_all
  exact hEq.tendsto
private theorem qkn_ratio_prod_tendsto_zero {k i j p q : ℕ} (hij : i < j) (hpq : p < q) :
    Filter.Tendsto
      (fun r : ℝ => ((qkn k i r : ℂ) / (qkn k j r : ℂ)) *
        ((qkn k p r : ℂ) / (qkn k q r : ℂ)))
      Filter.atTop (𝓝 (0 : ℂ)) := by
  simpa using (qkn_ratio_tendsto_zero (k := k) hij).mul (qkn_ratio_tendsto_zero (k := k) hpq)
private theorem qkn_self_ratio_prod_tendsto_one {k j q : ℕ} :
    Filter.Tendsto
      (fun r : ℝ => ((qkn k j r : ℂ) / (qkn k j r : ℂ)) *
        ((qkn k q r : ℂ) / (qkn k q r : ℂ)))
      Filter.atTop (𝓝 (1 : ℂ)) := by
  simpa using (qkn_self_ratio_tendsto_one (k := k) (d := j)).mul
    (qkn_self_ratio_tendsto_one (k := k) (d := q))
private lemma sum_ite_index_eq {d J : ℕ} (hJ : J < d + 1) (f : Fin (d + 1) → ℂ) :
    (∑ i : Fin (d + 1), if i.1 = J then f i else 0) = f ⟨J, hJ⟩ := by
  rw [Finset.sum_eq_single ⟨J, hJ⟩]
  · simp
  · intro i _ hi
    rw [if_neg fun h => hi (Fin.ext h)]
  · simp_all
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
private lemma exists_I_mul_of_re_eq_zero (z : ℂ) (hz : z.re = 0) :
    ∃ c : ℝ, z = Complex.I * (c : ℂ) := by
  refine ⟨z.im, ?_⟩
  apply Complex.ext <;> simp [hz]
private lemma fourierCoeff_mul_fourier
    (f : Circle → ℂ) (m n : ℤ) :
    fourierCoeff (fun t => f t * fourier n t) m = fourierCoeff f (m - n) := by
  simp [fourierCoeff, mul_assoc, mul_comm, sub_eq_add_neg]
private lemma fourierCoeff_star
    (f : Circle → ℂ) (m : ℤ) :
    fourierCoeff (fun t => star (f t)) m = star (fourierCoeff f (-m)) := by
  calc
    fourierCoeff (fun t => star (f t)) m
        = star (∫ t : Circle, fourier m t * f t ∂AddCircle.haarAddCircle) := by
          simpa [fourierCoeff, mul_comm, mul_left_comm, mul_assoc] using
            (integral_conj (μ := AddCircle.haarAddCircle)
              (f := fun t : Circle => fourier m t * f t))
    _ = star (fourierCoeff f (-m)) := by simp [fourierCoeff]
private theorem star_finiteCirclePoly_sum
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {r : ℝ} (hr : 0 < r) (t : Circle) :
    star (finiteCirclePoly k r a t) =
      ∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) * fourier (-(i.1 : ℤ)) t := by
  rw [finiteCirclePoly_sum (k := k) (a := a) (r := r) hr t]
  have hstar :
      star (∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t) =
        ∑ i : Fin (d + 1), star (a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t) := by simp
  rw [hstar]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hconj :
      (starRingEnd ℂ) ↑(AddCircle.toCircle ((i : ℕ) • t)) =
        ↑(AddCircle.toCircle (-((i : ℕ) • t))) := by
    rw [← Circle.coe_inv_eq_conj, ← AddCircle.toCircle_neg]
  simp [qkn_real, fourier_apply, hconj, mul_assoc, mul_left_comm, mul_comm]
private lemma continuous_circleSeries_hermiteCoeff
    {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) (r : ℝ) (hr : 0 < r) :
    Continuous (fun t : Circle => circleSeries k (hermiteCoeff k G) r t) := by
  rcases hermite_series_locally_uniform (k := k) (G := G) hG with ⟨g, hg, hcontG⟩
  have hCirclePoint : Continuous (fun t : Circle => circlePoint r t) := by
    unfold circlePoint
    exact continuous_const.mul (fourier (1 : ℤ)).continuous
  have hcontGt : Continuous (fun t : Circle => G (circlePoint r t)) :=
    hcontG.comp hCirclePoint
  have hnonzero : (circleLeadingFactor k r : ℂ) ≠ 0 := circleLeadingFactor_ne_zero k hr
  have hEq :
      circleSeries k (hermiteCoeff k G) r =
        fun t : Circle =>
          (circleLeadingFactor k r : ℂ)⁻¹ * (fourier (k : ℤ) t : ℂ) *
            G (circlePoint r t) := by
    funext t
    have hfour : (fourier (k : ℤ) t : ℂ) * (fourier (-(k : ℤ)) t : ℂ) = 1 := by
      rw [← fourier_add]
      simp
    have hrepr :=
      circle_representation_hermiteCoeff (k := k) (G := G) hG r hr t
    have hcancel :
        (circleLeadingFactor k r : ℂ)⁻¹ * (fourier (k : ℤ) t : ℂ) *
            ((circleLeadingFactor k r : ℂ) * (fourier (-(k : ℤ)) t : ℂ) *
              circleSeries k (hermiteCoeff k G) r t)
          = circleSeries k (hermiteCoeff k G) r t := by
      rw [show (circleLeadingFactor k r : ℂ)⁻¹ * (fourier (k : ℤ) t : ℂ) *
          ((circleLeadingFactor k r : ℂ) * (fourier (-(k : ℤ)) t : ℂ) *
            circleSeries k (hermiteCoeff k G) r t) =
          ((circleLeadingFactor k r : ℂ)⁻¹ * (circleLeadingFactor k r : ℂ)) *
            ((fourier (k : ℤ) t : ℂ) * (fourier (-(k : ℤ)) t : ℂ)) *
              circleSeries k (hermiteCoeff k G) r t by ring,
        inv_mul_cancel₀ hnonzero, hfour, one_mul, one_mul]
    rw [← hcancel, hrepr]
  rw [hEq]
  have hcontFour : Continuous (fun t : Circle => (fourier (k : ℤ) t : ℂ)) :=
    (fourier (k : ℤ)).continuous
  exact (continuous_const.mul hcontFour).mul hcontGt
private theorem fourierCoeff_circleSeries_mul_star_finiteCirclePoly
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ}
    (hG : G ∈ Hk k) {r : ℝ} (hr : 0 < r) (m : ℤ) :
    fourierCoeff (fun t : Circle =>
      circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)) m =
      ∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) *
        fourierCoeff (circleSeries k (hermiteCoeff k G) r) (m + i.1) := by
  have hfun :
      (fun t : Circle => circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)) =
        fun t : Circle =>
          ∑ i : Fin (d + 1),
            (star (a i) * (qkn k i.1 r : ℂ)) *
              (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t) := by
    funext t
    rw [star_finiteCirclePoly_sum a hr t, mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  rw [hfun]
  have hsum :=
    fourierCoeff.sum
      (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i : Fin (d + 1) =>
        fun t : Circle =>
          (star (a i) * (qkn k i.1 r : ℂ)) *
            (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t))
      (by
        intro i hi
        refine integrable_circle_of_continuous ?_
        have hc : Continuous (fun t : Circle => circleSeries k (hermiteCoeff k G) r t) :=
          continuous_circleSeries_hermiteCoeff hG r hr
        continuity)
  have hsum' := congrArg (fun F => F m) hsum
  rw [show (∑ i : Fin (d + 1),
        fun t : Circle =>
          (star (a i) * (qkn k i.1 r : ℂ)) *
            (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t)) =
      (fun t : Circle =>
        ∑ i : Fin (d + 1),
          (star (a i) * (qkn k i.1 r : ℂ)) *
            (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t)) by
      funext t
      simp [Finset.sum_apply]] at hsum'
  simp only [Finset.sum_apply] at hsum'
  rw [hsum']
  refine Finset.sum_congr rfl ?_
  intro i hi
  calc
    fourierCoeff
        (fun t : Circle =>
          (star (a i) * (qkn k i.1 r : ℂ)) *
            (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t)) m
      = (star (a i) * (qkn k i.1 r : ℂ)) *
          fourierCoeff (fun t : Circle =>
            circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t) m := by
            exact
              (fourierCoeff.const_mul (T := T)
                (f := fun t : Circle =>
                  circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t)
                (c := star (a i) * (qkn k i.1 r : ℂ)) (n := m))
    _ = (star (a i) * (qkn k i.1 r : ℂ)) *
          fourierCoeff (circleSeries k (hermiteCoeff k G) r) (m + i.1) := by
            rw [fourierCoeff_mul_fourier]
            norm_num
private theorem fourierCoeff_circleSeries_mul_star_finiteCirclePoly_nat
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ}
    (hG : G ∈ Hk k) {r : ℝ} (hr : 0 < r) (ell : ℕ) :
    fourierCoeff (fun t : Circle =>
      circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)) ell =
      ∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) *
        (hermiteCoeff k G (ell + i.1) * (qkn k (ell + i.1) r : ℂ)) := by
  rw [fourierCoeff_circleSeries_mul_star_finiteCirclePoly a hG hr ell]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hcoeff :=
    circleSeries_fourierCoeff_hermiteCoeff
      (k := k) (G := G) hG (r := r) hr (ell + i.1)
  simp_all
private lemma circleSeries_neg_fourierCoeff_eq_zero
    {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) {r : ℝ} (hr : 0 < r) :
    ∀ m : ℕ, fourierCoeff (circleSeries k (hermiteCoeff k G) r) (-(m + 1 : ℤ)) = 0 := by
  intro m
  let fcont : C(Circle, ℂ) :=
    ⟨circleSeries k (hermiteCoeff k G) r, continuous_circleSeries_hermiteCoeff hG r hr⟩
  let fLp := ContinuousMap.toLp (p := 2) AddCircle.haarAddCircle ℂ fcont
  let s : ℤ → ℝ := fun n => ‖fourierCoeff fLp n‖ ^ 2
  have hsummable : Summable s := by exact (hasSum_sq_fourierCoeff fLp).summable
  have hsummable_nat : Summable (fun n : ℕ => s n) :=
    hsummable.comp_injective Nat.cast_injective
  have hsummable_neg : Summable (fun n : ℕ => s (-(n + 1 : ℤ))) := by
    have hneginj : Function.Injective (fun n : ℕ => (-(n + 1 : ℤ))) := by
      intro x y h
      simp_all
    exact hsummable.comp_injective hneginj
  have hparseval :
      ∑' n : ℤ, s n = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
    have hIntEq :
        ∫ t : Circle, ‖fLp t‖ ^ 2 ∂AddCircle.haarAddCircle =
          circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
      unfold circleL2Sq
      refine integral_congr_ae ?_
      filter_upwards [ContinuousMap.coeFn_toAEEqFun (μ := AddCircle.haarAddCircle) fcont] with t ht
      simp [fcont, fLp, ht]
    calc
      ∑' n : ℤ, s n = ∫ t : Circle, ‖fLp t‖ ^ 2 ∂AddCircle.haarAddCircle := by
        exact (tsum_sq_fourierCoeff fLp)
      _ = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := hIntEq
  have hcoeff : ∀ n : ℕ, fourierCoeff fLp n = hermiteCoeff k G n * (qkn k n r : ℂ) := by
    intro n
    calc
      fourierCoeff fLp n = fourierCoeff fcont n := fourierCoeff_toLp (f := fcont) n
      _ = hermiteCoeff k G n * (qkn k n r : ℂ) :=
          circleSeries_fourierCoeff_hermiteCoeff (k := k) (G := G) hG (r := r) hr n
  have hnat_eq :
      ∑' n : ℕ, s n = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
    calc
      ∑' n : ℕ, s n = ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 * qkn k n r ^ 2 := by
        congr with n
        simp only [s, hcoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
          mul_comm]
      _ = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
        simpa [circleL2Sq] using
          (circleSeries_l2_identity_hermiteCoeff (k := k) (G := G) hG (r := r) hr).symm
  have hsplit :
      ∑' n : ℤ, s n = ∑' n : ℕ, s n + ∑' n : ℕ, s (-(n + 1 : ℤ)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (tsum_of_nat_of_neg_add_one (f := s) hsummable_nat hsummable_neg)
  have hneg_sum_zero : ∑' n : ℕ, s (-(n + 1 : ℤ)) = 0 := by
    linarith only [
      hparseval, hnat_eq, hsplit
    ]
  have htermle : s (-(m + 1 : ℤ)) ≤ ∑' n : ℕ, s (-(n + 1 : ℤ)) :=
    hsummable_neg.le_tsum m fun n _ => by
      dsimp [s]
      positivity
  have hsq : s (-(m + 1 : ℤ)) = 0 :=
    le_antisymm (hneg_sum_zero ▸ htermle) (by positivity)
  have hsqLp : fourierCoeff fLp (-(m + 1 : ℤ)) = 0 := by
    have hsq' : ‖fourierCoeff fLp (-(m + 1 : ℤ))‖ ^ 2 = 0 := by exact hsq
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq')
  exact (fourierCoeff_toLp (f := fcont) (-(m + 1 : ℤ))).symm.trans hsqLp
private theorem fourierCoeff_star_circleSeries_mul_star_finiteCirclePoly_nat
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ}
    (hG : G ∈ Hk k) {r : ℝ} (hr : 0 < r) (ell : ℕ) :
    fourierCoeff (fun t : Circle =>
      star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))) ell =
      ∑ i : Fin (d + 1),
        if _h : ell ≤ i.1 then
          star (hermiteCoeff k G (i.1 - ell)) * a i *
            ((qkn k i.1 r : ℂ) * (qkn k (i.1 - ell) r : ℂ))
        else 0 := by
  calc
    fourierCoeff (fun t : Circle =>
        star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))) ell
      = star (fourierCoeff (fun t : Circle =>
          circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)) (-ell)) := by
            simpa using
              (fourierCoeff_star
                (f := fun t : Circle =>
                  circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))
                (m := (ell : ℤ)))
    _ = star
          (∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) *
            fourierCoeff (circleSeries k (hermiteCoeff k G) r) ((-(ell : ℤ)) + i.1)) := by
          rw [fourierCoeff_circleSeries_mul_star_finiteCirclePoly (a := a) hG hr (-ell)]
    _ = ∑ i : Fin (d + 1),
          star
            (star (a i) * (qkn k i.1 r : ℂ) *
              fourierCoeff (circleSeries k (hermiteCoeff k G) r) ((-(ell : ℤ)) + i.1)) := by simp
    _ = ∑ i : Fin (d + 1),
          if h : ell ≤ i.1 then
            star (hermiteCoeff k G (i.1 - ell)) * a i *
              ((qkn k i.1 r : ℂ) * (qkn k (i.1 - ell) r : ℂ))
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases h : ell ≤ i.1
          · have hidx : (-(ell : ℤ)) + i.1 = ((i.1 - ell : ℕ) : ℤ) := by omega
            rw [hidx,
              circleSeries_fourierCoeff_hermiteCoeff (k := k) (G := G) hG (r := r) hr (i.1 - ell)]
            simp [h, qkn_real, mul_assoc, mul_left_comm, mul_comm]
          · have hidx : (-(ell : ℤ)) + i.1 = -((ell - i.1 - 1 : ℕ) + 1 : ℤ) := by omega
            rw [hidx,
              circleSeries_neg_fourierCoeff_eq_zero
                (k := k) (G := G) hG (r := r) hr (ell - i.1 - 1)]
            simp [h]
private lemma add_star_eq_zero_of_re_zero (z : ℂ) (hz : z.re = 0) : z + star z = 0 := by
  simp [Complex.ext_iff, hz]
private lemma scalar_factorization (c f s p : ℂ)
    (hc : star c = c) (hf : star f * f = 1) :
    (c * f * s) * star (c * f * p) = (c * c) * (s * star p) := by
  calc
    (c * f * s) * star (c * f * p)
        = c * f * s * (star p * (star f * star c)) := by simp [star_mul, mul_assoc]
    _ = c * f * s * (star p * (star f * c)) := by rw [hc]
    _ = c * c * (f * star f) * (s * star p) := by ring
    _ = (c * c) * (s * star p) := by rw [mul_comm f (star f), hf, mul_one]
private theorem circleSeries_star_finiteCirclePoly_add_star_eq_zero
    {k d : ℕ} (a : Fin (d + 1) → ℂ)
    {G : ℂ → ℂ}
    (hG : G ∈ Hk k)
    (hzero : ∀ z : ℂ, Complex.re (G z * star (finiteHermiteSum k a z)) = 0)
    {r : ℝ} (hr : 0 < r) (t : Circle) :
    circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t) +
      star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)) = 0 := by
  let c : ℂ := circleLeadingFactor k r
  let f : ℂ := (fourier (-(k : ℤ)) t : ℂ)
  let s : ℂ := circleSeries k (hermiteCoeff k G) r t
  let p : ℂ := finiteCirclePoly k r a t
  have hGrep := circle_representation_hermiteCoeff (k := k) (G := G) hG r hr t
  have hUrep := finiteHermiteSum_circle (k := k) (a := a) (r := r) hr t
  have hz : Complex.re ((c * f * s) * star (c * f * p)) = 0 := by
    simpa [c, f, s, p, hGrep, hUrep, mul_assoc] using hzero (circlePoint r t)
  have hmain : (c * f * s) * star (c * f * p) + star ((c * f * s) * star (c * f * p)) = 0 :=
    add_star_eq_zero_of_re_zero _ hz
  have hc : star c = c := by simp [c, circleLeadingFactor]
  have hf : star f * f = 1 := by
    have hmul : star f * f = ‖f‖ ^ 2 := by simpa [sq] using (RCLike.conj_mul f)
    rw [hmul, show ‖f‖ = 1 by simp [f, fourier_apply, Circle.norm_coe]]
    norm_num
  have hcc : star (c * c) = c * c := by simp [hc]
  have hx : (c * f * s) * star (c * f * p) = (c * c) * (s * star p) :=
    scalar_factorization c f s p hc hf
  have hfact : (c * c) * (s * star p) + (c * c) * star (s * star p) = 0 := by
    have hrew : star ((c * c) * (s * star p)) = (c * c) * star (s * star p) := by
      simp_all
    rw [hx, hrew] at hmain
    exact hmain
  have hcz : c ≠ 0 := circleLeadingFactor_ne_zero k hr
  have hcnz : (c * c) ≠ 0 := mul_ne_zero hcz hcz
  have hsplit : (c * c) * ((s * star p) + star (s * star p)) = 0 := by
    simpa [mul_add, mul_assoc] using hfact
  exact (mul_eq_zero.mp hsplit).resolve_left hcnz
private theorem positive_mode_mixed_eq_zero
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ}
    (hG : G ∈ Hk k)
    (hzero : ∀ z : ℂ, Complex.re (G z * star (finiteHermiteSum k a z)) = 0)
    {r : ℝ} (hr : 0 < r) (ell : ℕ) :
    (∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) *
      (hermiteCoeff k G (ell + i.1) * (qkn k (ell + i.1) r : ℂ))) +
    (∑ i : Fin (d + 1),
      if _h : ell ≤ i.1 then
        star (hermiteCoeff k G (i.1 - ell)) * a i *
          ((qkn k i.1 r : ℂ) * (qkn k (i.1 - ell) r : ℂ))
      else 0) = 0 := by
  have hfun :
      (fun t : Circle =>
        circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t) +
          star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))) =
      fun _ : Circle => (0 : ℂ) := by
    funext t
    exact circleSeries_star_finiteCirclePoly_add_star_eq_zero
      (k := k) (d := d) (a := a) hG hzero hr t
  have hcoeff0 :
      fourierCoeff
        (fun t : Circle =>
          circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t) +
            star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)))
        ell = 0 := by
    rw [hfun]
    simp [fourierCoeff]
  let f : Circle → ℂ :=
    fun t : Circle => circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)
  let g : Circle → ℂ := fun t : Circle => star (f t)
  have hp : Continuous (fun t : Circle => finiteCirclePoly k r a t) := by
    let F : Circle → ℂ :=
      fun t : Circle => ∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t
    have hF : Continuous F := by
      classical
      refine continuous_finsetSum _ ?_
      intro i hi
      continuity
    have hEq : (fun t : Circle => finiteCirclePoly k r a t) = F := by
      funext t
      simp [F, finiteCirclePoly_sum (k := k) (a := a) (r := r) hr t]
    simp_all only []
  have hcontf : Continuous f :=
    (continuous_circleSeries_hermiteCoeff hG r hr).mul hp.star
  have hf : Integrable f AddCircle.haarAddCircle := integrable_circle_of_continuous hcontf
  have hg : Integrable g AddCircle.haarAddCircle := integrable_circle_of_continuous hcontf.star
  have hadd :
      fourierCoeff
          (fun t : Circle =>
            circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t) +
              star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))) ell =
        fourierCoeff
            (fun t : Circle =>
              circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))
            ell +
          fourierCoeff
            (fun t : Circle =>
              star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)))
            ell := by
    have haddfun := fourierCoeff.add (T := T) (f := f) (g := g) hf hg
    exact congrArg (fun F => F ell) haddfun
  rw [hadd,
    fourierCoeff_circleSeries_mul_star_finiteCirclePoly_nat (a := a) hG hr ell,
    fourierCoeff_star_circleSeries_mul_star_finiteCirclePoly_nat (a := a) hG hr ell] at hcoeff0
  exact hcoeff0
private theorem positive_mode_main_sum_tendsto
    {k d ell : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ} :
    Filter.Tendsto
      (fun r : ℝ =>
        ∑ i : Fin (d + 1),
          star (a i) * hermiteCoeff k G (ell + i.1) *
            (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k (ell + i.1) r : ℂ) / (qkn k (d + ell) r : ℂ))))
      Filter.atTop
      (𝓝 (star (topCoeff a) * hermiteCoeff k G (d + ell))) := by
  have hsum :
      Filter.Tendsto
        (fun r : ℝ =>
          ∑ i : Fin (d + 1),
            star (a i) * hermiteCoeff k G (ell + i.1) *
              (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
                ((qkn k (ell + i.1) r : ℂ) / (qkn k (d + ell) r : ℂ))))
        Filter.atTop
        (𝓝
          (∑ i : Fin (d + 1), if i.1 = d then star (a i) * hermiteCoeff k G (d + ell) else 0)) := by
    refine tendsto_finsetSum (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i : Fin (d + 1) => fun r : ℝ =>
        star (a i) * hermiteCoeff k G (ell + i.1) *
          (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
            ((qkn k (ell + i.1) r : ℂ) / (qkn k (d + ell) r : ℂ))))
      (a := fun i : Fin (d + 1) =>
        if i.1 = d then star (a i) * hermiteCoeff k G (d + ell) else 0) ?_
    intro i hi
    by_cases hid : i.1 = d
    · have hratio : Filter.Tendsto
          (fun r : ℝ =>
            ((qkn k d r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k (ell + d) r : ℂ) / (qkn k (d + ell) r : ℂ)))
          Filter.atTop (𝓝 (1 : ℂ)) := by
        simpa [Nat.add_comm] using qkn_self_ratio_prod_tendsto_one (k := k) (j := d) (q := d + ell)
      have hi_eq : i = ⟨d, Nat.lt_succ_self d⟩ := Fin.ext hid
      subst hi_eq
      simpa [topCoeff, Nat.add_comm, mul_assoc] using
        (hratio.const_mul (star (a ⟨d, Nat.lt_succ_self d⟩) * hermiteCoeff k G (d + ell)))
    · have hi_lt : i.1 < d := lt_of_le_of_ne (Nat.le_of_lt_succ i.2) hid
      have hless : ell + i.1 < d + ell := by omega
      simpa [hid, mul_assoc] using
        ((qkn_ratio_prod_tendsto_zero (k := k) hi_lt hless).const_mul
          (star (a i) * hermiteCoeff k G (ell + i.1)))
  have htop :
      (∑ i : Fin (d + 1), if i.1 = d then star (a i) * hermiteCoeff k G (d + ell) else 0) =
        star (topCoeff a) * hermiteCoeff k G (d + ell) := by
    rw [sum_ite_index_eq (Nat.lt_succ_self d)]
    simp [topCoeff]
  exact htop ▸ hsum
private theorem positive_mode_error_sum_tendsto_zero
    {k d ell : ℕ} (hEll : 1 ≤ ell) (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ} :
    Filter.Tendsto
      (fun r : ℝ =>
        ∑ i : Fin (d + 1),
        if _h : ell ≤ i.1 then
          star (hermiteCoeff k G (i.1 - ell)) * a i *
            (((qkn k i.1 r : ℂ) / (qkn k (d + ell) r : ℂ)) *
              ((qkn k (i.1 - ell) r : ℂ) / (qkn k d r : ℂ)))
        else 0)
      Filter.atTop (𝓝 (0 : ℂ)) := by
  have hsum :
      Filter.Tendsto
        (fun r : ℝ =>
          ∑ i : Fin (d + 1),
            if h : ell ≤ i.1 then
              star (hermiteCoeff k G (i.1 - ell)) * a i *
                (((qkn k i.1 r : ℂ) / (qkn k (d + ell) r : ℂ)) *
                  ((qkn k (i.1 - ell) r : ℂ) / (qkn k d r : ℂ)))
            else 0)
        Filter.atTop (𝓝 (∑ _ : Fin (d + 1), (0 : ℂ))) := by
    refine tendsto_finsetSum (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i : Fin (d + 1) => fun r : ℝ =>
        if h : ell ≤ i.1 then
          star (hermiteCoeff k G (i.1 - ell)) * a i *
            (((qkn k i.1 r : ℂ) / (qkn k (d + ell) r : ℂ)) *
              ((qkn k (i.1 - ell) r : ℂ) / (qkn k d r : ℂ)))
        else 0)
      (a := fun _ : Fin (d + 1) => (0 : ℂ)) ?_
    intro i hi
    by_cases h : ell ≤ i.1
    · have hi_lt : i.1 < d + ell := by omega
      have hlt : i.1 - ell < d := by
        have hi_le : i.1 ≤ d := Nat.le_of_lt_succ i.2
        omega
      simpa [h, mul_assoc] using
        ((qkn_ratio_prod_tendsto_zero (k := k) hi_lt hlt).const_mul
          (star (hermiteCoeff k G (i.1 - ell)) * a i))
    · simp [h]
  simpa using hsum
private theorem high_coeff_vanish
    {k d ell : ℕ} (hEll : 1 ≤ ell) (a : Fin (d + 1) → ℂ) (hTop : topCoeff a ≠ 0)
    {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hzero : ∀ z : ℂ, Complex.re (G z * star (finiteHermiteSum k a z)) = 0) :
    hermiteCoeff k G (d + ell) = 0 := by
  let F : ℝ → ℂ :=
    fun r : ℝ =>
      (∑ i : Fin (d + 1),
        star (a i) * hermiteCoeff k G (ell + i.1) *
          (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
            ((qkn k (ell + i.1) r : ℂ) / (qkn k (d + ell) r : ℂ)))) +
      (∑ i : Fin (d + 1),
        if h : ell ≤ i.1 then
          star (hermiteCoeff k G (i.1 - ell)) * a i *
            (((qkn k i.1 r : ℂ) / (qkn k (d + ell) r : ℂ)) *
              ((qkn k (i.1 - ell) r : ℂ) / (qkn k d r : ℂ)))
        else 0)
  have hFtendsto :
      Filter.Tendsto F Filter.atTop (𝓝 (star (topCoeff a) * hermiteCoeff k G (d + ell))) := by
    simpa only [add_zero] using
      (positive_mode_main_sum_tendsto (k := k) (d := d) (ell := ell) (a := a) (G := G)).add
        (positive_mode_error_sum_tendsto_zero (k := k) (d := d) (ell := ell) hEll (a := a) (G := G))
  obtain ⟨Rd, hRd, hd_nonzero⟩ := qkn_eventually_nonzero k d
  obtain ⟨Rn, hRn, hn_nonzero⟩ := qkn_eventually_nonzero k (d + ell)
  have hFzero : F =ᶠ[Filter.atTop] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop Rd, Filter.eventually_ge_atTop Rn] with r hrD hrN
    have hd : (qkn k d r : ℂ) ≠ 0 := by exact_mod_cast hd_nonzero r hrD
    have hn : (qkn k (d + ell) r : ℂ) ≠ 0 := by exact_mod_cast hn_nonzero r hrN
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_trans hRd hrD)
    have hraw := positive_mode_mixed_eq_zero (k := k) (d := d) (a := a) hG hzero (r := r) hr ell
    have hEq : ((qkn k d r : ℂ) * (qkn k (d + ell) r : ℂ)) * F r = 0 := by
      have hNorm :
          ((qkn k d r : ℂ) * (qkn k (d + ell) r : ℂ)) * F r =
            (∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) *
              (hermiteCoeff k G (ell + i.1) * (qkn k (ell + i.1) r : ℂ))) +
            (∑ i : Fin (d + 1), if h : ell ≤ i.1 then
              star (hermiteCoeff k G (i.1 - ell)) * a i *
                ((qkn k i.1 r : ℂ) * (qkn k (i.1 - ell) r : ℂ)) else 0) := by
        dsimp [F]
        rw [mul_add]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          field_simp [hd, hn]
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases h : ell ≤ i.1
          · simp [h]
            field_simp [hd, hn]
          · simp [h]
      exact hNorm.trans hraw
    simp_all
  have hzero_tendsto : Filter.Tendsto F Filter.atTop (𝓝 (0 : ℂ)) := by simpa using hFzero.tendsto
  have hlim : star (topCoeff a) * hermiteCoeff k G (d + ell) = 0 := by
    simpa [zero_add] using
      (tendsto_nhds_unique (f := F) (l := Filter.atTop) hFtendsto hzero_tendsto)
  simp_all
private theorem finite_positive_mode_main_tendsto
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) :
    Filter.Tendsto
      (fun r : ℝ => finitePositiveModeMainSum k d a b n r)
      Filter.atTop (𝓝 (star (a n) * b ⟨d, Nat.lt_succ_self d⟩)) := by
  have hsum :
      Filter.Tendsto
        (fun r : ℝ => finitePositiveModeMainSum k d a b n r)
        Filter.atTop
        (𝓝
          (∑ i : Fin (d + 1),
            if i.1 = n.1 then star (a i) * b ⟨d, Nat.lt_succ_self d⟩ else 0)) := by
    refine tendsto_finsetSum (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i : Fin (d + 1) => fun r : ℝ =>
        star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
          (((qkn k i.1 r : ℂ) / (qkn k n.1 r : ℂ)) *
            ((qkn k (d - n.1 + i.1) r : ℂ) / (qkn k d r : ℂ))))
      (a := fun i : Fin (d + 1) =>
        if i.1 = n.1 then star (a i) * b ⟨d, Nat.lt_succ_self d⟩ else 0) ?_
    intro i hi
    by_cases hi_eq : i.1 = n.1
    · have hi_eq' : i = n := Fin.ext hi_eq
      subst i
      have hidx : d - n.1 + n.1 = d := by omega
      have hlt : d - n.1 + n.1 < d + 1 := by omega
      have hratio :
          Filter.Tendsto
            (fun r : ℝ =>
              ((qkn k n.1 r : ℂ) / (qkn k n.1 r : ℂ)) *
                ((qkn k (d - n.1 + n.1) r : ℂ) / (qkn k d r : ℂ)))
            Filter.atTop (𝓝 (1 : ℂ)) := by
        simpa [hidx] using qkn_self_ratio_prod_tendsto_one (k := k) (j := n.1) (q := d)
      simpa [finitePositiveModeMainSum, hidx, hlt, mul_assoc] using
        (hratio.const_mul (star (a n) * b ⟨d, Nat.lt_succ_self d⟩))
    · by_cases hi_lt : i.1 < n.1
      · have hless2 : d - n.1 + i.1 < d := by omega
        have hlt : d - n.1 + i.1 < d + 1 := by omega
        simpa [hi_eq, hi_lt, hlt, finitePositiveModeMainSum, mul_assoc] using
          ((qkn_ratio_prod_tendsto_zero (k := k) hi_lt hless2).const_mul
            (star (a i) * b ⟨d - n.1 + i.1, by omega⟩))
      · have hnot : ¬ d - n.1 + i.1 < d + 1 := by omega
        simp only [hi_eq, dif_neg hnot, mul_zero, zero_mul]
        exact tendsto_const_nhds
  have htop :
      (∑ i : Fin (d + 1), if i.1 = n.1 then star (a i) * b ⟨d, Nat.lt_succ_self d⟩ else 0) =
        star (a n) * b ⟨d, Nat.lt_succ_self d⟩ := by rw [sum_ite_index_eq n.2]
  exact htop ▸ hsum
private theorem finite_positive_mode_error_tendsto
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) :
    Filter.Tendsto
      (fun r : ℝ => finitePositiveModeErrorSum k d a b n r)
      Filter.atTop (𝓝 (star (b n) * a ⟨d, Nat.lt_succ_self d⟩)) := by
  have hsum :
      Filter.Tendsto
        (fun r : ℝ => finitePositiveModeErrorSum k d a b n r)
        Filter.atTop
        (𝓝 (∑ i : Fin (d + 1), if i.1 = d then star (b n) * a i else 0)) := by
    refine tendsto_finsetSum (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i : Fin (d + 1) => fun r : ℝ =>
        if h : d - n.1 ≤ i.1 then
          star (b ⟨i.1 - (d - n.1), by
            have hi : i.1 ≤ d := Nat.le_of_lt_succ i.2
            omega⟩) * a i *
            (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k (i.1 - (d - n.1)) r : ℂ) / (qkn k n.1 r : ℂ)))
        else 0)
      (a := fun i : Fin (d + 1) => if i.1 = d then star (b n) * a i else 0) ?_
    intro i hi
    by_cases hi_eq : i.1 = d
    · have hi_eq' : i = ⟨d, Nat.lt_succ_self d⟩ := Fin.ext hi_eq
      subst i
      have hidx : d - (d - n.1) = n.1 := by omega
      have hge : d - n.1 ≤ d := by omega
      have hratio :
          Filter.Tendsto
            (fun r : ℝ =>
              ((qkn k d r : ℂ) / (qkn k d r : ℂ)) *
                ((qkn k (d - (d - n.1)) r : ℂ) / (qkn k n.1 r : ℂ)))
            Filter.atTop (𝓝 (1 : ℂ)) := by
        simpa [hidx] using qkn_self_ratio_prod_tendsto_one (k := k) (j := d) (q := n.1)
      simpa [finitePositiveModeErrorSum, hidx, hge, mul_assoc] using
        (hratio.const_mul (star (b n) * a ⟨d, Nat.lt_succ_self d⟩))
    · have hi_lt : i.1 < d := lt_of_le_of_ne (Nat.le_of_lt_succ i.2) hi_eq
      by_cases hi_ge : d - n.1 ≤ i.1
      · have hless2 : i.1 - (d - n.1) < n.1 := by omega
        simpa [hi_eq, hi_ge, finitePositiveModeErrorSum, mul_assoc] using
          ((qkn_ratio_prod_tendsto_zero (k := k) hi_lt hless2).const_mul
            (star (b ⟨i.1 - (d - n.1), by
              have hi : i.1 ≤ d := Nat.le_of_lt_succ i.2
              omega⟩) * a i))
      · simp [hi_eq, hi_ge]
  have htop :
      (∑ i : Fin (d + 1), if i.1 = d then star (b n) * a i else 0) =
        star (b n) * a ⟨d, Nat.lt_succ_self d⟩ := by rw [sum_ite_index_eq (Nat.lt_succ_self d)]
  exact htop ▸ hsum
private theorem finite_positive_mode_main_raw
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) {r : ℝ} :
    (∑ i : Fin (d + 1),
      star (a i) * (qkn k i.1 r : ℂ) *
        (hermiteCoeff k (finiteHermiteSum k b) (d - n.1 + i.1) * (qkn k (d - n.1 + i.1) r : ℂ))) =
    ∑ i : Fin (d + 1),
      star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
        ((qkn k i.1 r : ℂ) * (qkn k (d - n.1 + i.1) r : ℂ)) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hidx : d - n.1 + i.1 < d + 1
  · simp [hermiteCoeff_finiteHermiteSum, hidx, mul_assoc, mul_left_comm, mul_comm]
  · simp [hermiteCoeff_finiteHermiteSum, hidx, mul_left_comm, mul_comm]
private theorem finite_positive_mode_error_raw
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) {r : ℝ} :
    (∑ i : Fin (d + 1),
      if _h : d - n.1 ≤ i.1 then
        star (hermiteCoeff k (finiteHermiteSum k b) (i.1 - (d - n.1))) * a i *
          ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ))
      else 0) =
    ∑ i : Fin (d + 1),
      if h : d - n.1 ≤ i.1 then
        star (b ⟨i.1 - (d - n.1), by
          have _hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
          omega⟩) * a i *
          ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ))
      else 0 := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : d - n.1 ≤ i.1
  · have hlt : i.1 - (d - n.1) < d + 1 := by
      have hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
      omega
    simp [h, hermiteCoeff_finiteHermiteSum, hlt]
  · simp [h]
private theorem finitePositiveModeMainSum_mul_den
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) {r : ℝ}
    (hd : (qkn k d r : ℂ) ≠ 0) (hn : (qkn k n.1 r : ℂ) ≠ 0) :
    ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * finitePositiveModeMainSum k d a b n r =
      ∑ i : Fin (d + 1),
        star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
          ((qkn k i.1 r : ℂ) * (qkn k (d - n.1 + i.1) r : ℂ)) := by
  unfold finitePositiveModeMainSum
  rw [mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hidx : d - n.1 + i.1 < d + 1
  · simp [hidx, mul_assoc, mul_comm]
    field_simp [hd, hn]
  · simp [hidx]
private theorem finitePositiveModeErrorSum_mul_den
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) {r : ℝ}
    (hd : (qkn k d r : ℂ) ≠ 0) (hn : (qkn k n.1 r : ℂ) ≠ 0) :
    ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * finitePositiveModeErrorSum k d a b n r =
      ∑ i : Fin (d + 1),
        if h : d - n.1 ≤ i.1 then
          star (b ⟨i.1 - (d - n.1), by
            have _hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
            omega⟩) * a i *
            ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ))
        else 0 := by
  unfold finitePositiveModeErrorSum
  rw [mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : d - n.1 ≤ i.1
  · have hcalc :
        ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) *
            (star (b ⟨i.1 - (d - n.1), by
              have hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
              omega⟩) * a i *
              (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
                ((qkn k (i.1 - (d - n.1)) r : ℂ) / (qkn k n.1 r : ℂ)))) =
          star (b ⟨i.1 - (d - n.1), by
            have hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
            omega⟩) * a i * ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ)) := by
      field_simp [hd, hn]
    simpa [h, mul_assoc, mul_left_comm, mul_comm] using hcalc
  · simp [h]
private theorem finite_positive_mode_relation
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1))
    (hzero : ∀ z : ℂ, Complex.re (finiteHermiteSum k b z * star (finiteHermiteSum k a z)) = 0) :
    star (a n) * b ⟨d, Nat.lt_succ_self d⟩ + star (b n) * a ⟨d, Nat.lt_succ_self d⟩ = 0 := by
  let ell : ℕ := d - n.1
  let F : ℝ → ℂ :=
    fun r : ℝ => finitePositiveModeMainSum k d a b n r + finitePositiveModeErrorSum k d a b n r
  have hFtendsto : Filter.Tendsto F Filter.atTop
      (𝓝 (star (a n) * b ⟨d, Nat.lt_succ_self d⟩ + star (b n) * a ⟨d, Nat.lt_succ_self d⟩)) := by
    exact (finite_positive_mode_main_tendsto (k := k) (d := d) a b n).add
      (finite_positive_mode_error_tendsto (k := k) (d := d) a b n)
  obtain ⟨Rd, hRd, hd_nonzero⟩ := qkn_eventually_nonzero k d
  obtain ⟨Rn, hRn, hn_nonzero⟩ := qkn_eventually_nonzero k n.1
  have hFzero : F =ᶠ[Filter.atTop] fun _ : ℝ => (0 : ℂ) := by
    have hG : finiteHermiteSum k b ∈ Hk k := finiteHermiteSum_mem_Hk k b
    filter_upwards [Filter.eventually_ge_atTop Rd, Filter.eventually_ge_atTop Rn] with r hrD hrN
    have hd : (qkn k d r : ℂ) ≠ 0 := by exact_mod_cast hd_nonzero r hrD
    have hn : (qkn k n.1 r : ℂ) ≠ 0 := by exact_mod_cast hn_nonzero r hrN
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_trans hRd hrD)
    have hraw := positive_mode_mixed_eq_zero (k := k) (d := d) (a := a) (G := finiteHermiteSum k b)
      hG hzero (r := r) hr ell
    have hraw0 :
        (∑ i : Fin (d + 1),
          star (a i) * (qkn k i.1 r : ℂ) *
            (hermiteCoeff k (finiteHermiteSum k b) (d - n.1 + i.1) *
              (qkn k (d - n.1 + i.1) r : ℂ))) +
        (∑ i : Fin (d + 1),
          if h : d - n.1 ≤ i.1 then
            star (hermiteCoeff k (finiteHermiteSum k b) (i.1 - (d - n.1))) * a i *
              ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ))
          else 0) = 0 := by exact hraw
    rw [finite_positive_mode_main_raw (k := k) (d := d) (a := a) (b := b) n (r := r),
      finite_positive_mode_error_raw (k := k) (d := d) (a := a) (b := b) n (r := r)] at hraw0
    have hEq : ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * F r = 0 := by
      calc
        ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * F r
            = ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * finitePositiveModeMainSum k d a b n r +
                ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * finitePositiveModeErrorSum k d a b n r := by
                  dsimp [F]
                  ring
        _ = (∑ i : Fin (d + 1),
              star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
                ((qkn k i.1 r : ℂ) * (qkn k (d - n.1 + i.1) r : ℂ))) +
              (∑ i : Fin (d + 1),
                if h : d - n.1 ≤ i.1 then
                  star (b ⟨i.1 - (d - n.1), by
                    have hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
                    omega⟩) * a i * ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ))
                else 0) := by
                  rw [finitePositiveModeMainSum_mul_den (k := k) (d := d) (a := a) (b := b) n hd hn,
                    finitePositiveModeErrorSum_mul_den (k := k) (d := d) (a := a) (b := b) n hd hn]
        _ = 0 := hraw0
    exact (mul_eq_zero.mp hEq).resolve_left (mul_ne_zero hd hn)
  have hzero_tendsto : Filter.Tendsto F Filter.atTop (𝓝 (0 : ℂ)) := by exact hFzero.tendsto
  exact (tendsto_nhds_unique (f := F) (l := Filter.atTop) hFtendsto hzero_tendsto)
private theorem finite_real_part_rigidity
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (hTop : topCoeff a ≠ 0)
    (hzero : ∀ z : ℂ, Complex.re (finiteHermiteSum k b z * star (finiteHermiteSum k a z)) = 0) :
    ∃ c : ℝ, finiteHermiteSum k b = ((Complex.I * (c : ℂ)) • finiteHermiteSum k a) := by
  let top : Fin (d + 1) := ⟨d, Nat.lt_succ_self d⟩
  let lam : ℂ := b top / a top
  have htopA : a top ≠ 0 := by simpa [top, topCoeff] using hTop
  have htop_eq : b top = lam * a top := by
    dsimp [lam]
    field_simp [htopA]
  have hrel : ∀ n : Fin (d + 1), star (a n) * b top + star (b n) * a top = 0 := by
    intro n
    exact finite_positive_mode_relation (k := k) a b n hzero
  have hlam_add_star : lam + star lam = 0 := by
    have hrel_top := hrel top
    have hsq_nonzero : star (a top) * a top ≠ 0 :=
      mul_ne_zero (mt star_eq_zero.mp htopA) htopA
    have htmp : (lam + star lam) * (star (a top) * a top) = 0 := by
      calc
        (lam + star lam) * (star (a top) * a top)
            = star (a top) * (lam * a top) + star (lam * a top) * a top := by
                rw [star_mul]
                ring_nf
        _ = star (a top) * b top + star (b top) * a top := by rw [htop_eq]
        _ = 0 := hrel_top
    exact (mul_eq_zero.mp htmp).resolve_right hsq_nonzero
  have hlam_re : lam.re = 0 := by
    have hre := congrArg Complex.re hlam_add_star
    simp at hre
    linarith only [hre]
  obtain ⟨c, hc⟩ := exists_I_mul_of_re_eq_zero lam hlam_re
  have hstar_lam : star lam = -lam := by simp [hc, mul_comm]
  have hb_coeff : ∀ n : Fin (d + 1), b n = lam * a n := by
    intro n
    have hrel' : star (b n) + lam * star (a n) = 0 := by
      have htmp' : (star (b n) + lam * star (a n)) * a top = 0 := by
        calc
          (star (b n) + lam * star (a n)) * a top
              = star (a n) * (lam * a top) + star (b n) * a top := by ring_nf
          _ = star (a n) * b top + star (b n) * a top := by rw [htop_eq]
          _ = 0 := hrel n
      exact (mul_eq_zero.mp htmp').resolve_right htopA
    have hstar := congrArg star hrel'
    have htmp : b n + star lam * a n = 0 := by
      simpa [star_add, star_mul, mul_assoc, mul_left_comm, mul_comm] using hstar
    rw [eq_neg_iff_add_eq_zero.mpr htmp, hstar_lam, neg_mul, neg_neg]
  refine ⟨c, ?_⟩
  funext z
  calc
    finiteHermiteSum k b z
        = ∑ n : Fin (d + 1), (lam * a n) * Phi k n.1 z := by simp [finiteHermiteSum, hb_coeff]
    _ = lam * ∑ n : Fin (d + 1), a n * Phi k n.1 z := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro n hn
          ring
    _ = (Complex.I * (c : ℂ)) * ∑ n : Fin (d + 1), a n * Phi k n.1 z := by simp [hc]
    _ = ((Complex.I * (c : ℂ)) • finiteHermiteSum k a) z := by
          simp [finiteHermiteSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
            mul_left_comm]
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
      (a : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0)
      {G : ℂ → ℂ},
        G ∈ Hk k →
          (∀ z : ℂ, Complex.re (G z * star (finiteHermiteSum k a z)) = 0) →
            ∃ c : ℝ, G = ((Complex.I * (c : ℂ)) • finiteHermiteSum k a) := by
  intro k d a hTop G hG hzero
  let b : Fin (d + 1) → ℂ := fun n => hermiteCoeff k G n.1
  have hvanish : ∀ n : ℕ, d < n → hermiteCoeff k G n = 0 := by
    intro n hn
    have hEll : 1 ≤ n - d := by omega
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hn)] using
      (high_coeff_vanish (k := k) (d := d) (ell := n - d) (a := a) hEll hTop hG hzero)
  have htrunc : G = truncate k d G := by
    apply truncate_unique (k := k) (J := d) (G := G) (H := G) hG
    simp_all
  have hG_eq : G = finiteHermiteSum k b :=
    htrunc.trans (by simp [truncate_eq_finiteHermiteSum, b])
  have hzero' :
      ∀ z : ℂ, Complex.re (finiteHermiteSum k b z * star (finiteHermiteSum k a z)) = 0 := by
    intro z
    simpa [hG_eq] using hzero z
  obtain ⟨c, hfin⟩ := finite_real_part_rigidity (k := k) (d := d) (a := a) (b := b) hTop hzero'
  refine ⟨c, ?_⟩
  simpa [hG_eq] using hfin
end HermitekLEAN
