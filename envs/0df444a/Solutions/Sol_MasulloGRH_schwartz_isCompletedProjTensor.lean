-- Prove2me | solution 1 for MasulloGRH.schwartz_isCompletedProjTensor
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-22T15:14:16.190862+00:00
-- url     : https://prove2.me/submissions/41b7173d-420d-4707-9977-b14a26adeefe

import Definitions.Def_TopologicalTensorProduct_Completion

set_option autoImplicit false

universe u

namespace MasulloGRHSchwartzKernelAux

open Topology Filter Set FourierTransform MeasureTheory

noncomputable section

/-! ### one-dimensional cutoffs -/

def sig (t : ℝ) : ℝ := Real.smoothTransition (4 * t)

lemma sig_zero {t : ℝ} (h : t ≤ 0) : sig t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma sig_one {t : ℝ} (h : 1 / 4 ≤ t) : sig t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma sig_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sig :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)

/-- the partition-of-unity profile -/
def psi (t : ℝ) : ℝ := sig (t + 3 / 8) - sig (t - 1 / 8)

lemma psi_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi :=
  (sig_smooth.comp (contDiff_id.add contDiff_const)).sub
    (sig_smooth.comp (contDiff_id.sub contDiff_const))

lemma psi_zero {t : ℝ} (h : 3 / 8 ≤ |t|) : psi t = 0 := by
  rcases le_abs'.1 h with h | h
  · rw [psi, sig_zero (by linarith), sig_zero (by linarith), sub_zero]
  · rw [psi, sig_one (by linarith), sig_one (by linarith), sub_self]

lemma psi_sum_Icc (t : ℝ) :
    ∑ k ∈ Finset.Icc (⌊2 * t⌋ - 2) (⌊2 * t⌋ + 2), psi (t - k / 2) = 1 := by
  set a := ⌊2 * t⌋ with ha
  have h1 : (a : ℝ) ≤ 2 * t := Int.floor_le _
  have h2 : 2 * t < a + 1 := Int.lt_floor_add_one _
  have e : ∀ k : ℤ, psi (t - k / 2) = sig (t - k / 2 + 3 / 8) - sig (t - ((k + 1 : ℤ) : ℝ) / 2 + 3 / 8) := by
    intro k
    rw [psi]
    congr 2
    push_cast
    ring
  simp_rw [e]
  have hI : Finset.Icc (a - 2) (a + 2) = {a - 2, a - 1, a, a + 1, a + 2} := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [hI]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_singleton]
  push_cast
  ring_nf
  rw [sig_one (by linarith), sig_zero (by linarith)]
  ring

lemma psi_hasSum (t : ℝ) : HasSum (fun k : ℤ => psi (t - k / 2)) 1 := by
  rw [← psi_sum_Icc t]
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  apply psi_zero
  have h1 : ((⌊2 * t⌋ : ℤ) : ℝ) ≤ 2 * t := Int.floor_le _
  have h2 : 2 * t < ⌊2 * t⌋ + 1 := Int.lt_floor_add_one _
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with hk | hk
  · have : (k : ℝ) ≤ ⌊2 * t⌋ - 3 := by exact_mod_cast (by omega : k ≤ ⌊2 * t⌋ - 3)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (⌊2 * t⌋ : ℝ) + 3 ≤ k := by exact_mod_cast (by omega : ⌊2 * t⌋ + 3 ≤ k)
    rw [abs_of_neg (by linarith)]
    linarith

/-- the plateau profile, equal to one on `[-3/8, 3/8]` and vanishing off `(-7/16, 7/16)` -/
def rho (t : ℝ) : ℝ := Real.smoothTransition (16 * (t + 7 / 16)) * Real.smoothTransition (16 * (7 / 16 - t))

lemma rho_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rho :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.add contDiff_const))).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))

lemma rho_one {t : ℝ} (h : |t| ≤ 3 / 8) : rho t = 1 := by
  rw [abs_le] at h
  rw [rho, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

lemma rho_zero {t : ℝ} (h : 7 / 16 ≤ |t|) : rho t = 0 := by
  rcases le_abs'.1 h with h | h
  · rw [rho, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [rho, Real.smoothTransition.zero_of_nonpos (x := 16 * (7 / 16 - t)) (by linarith), mul_zero]


/-! ### cutoffs on `ℝ^m` -/

variable {m : ℕ}

abbrev V (m : ℕ) := EuclideanSpace ℝ (Fin m)

def chi (x : V m) : ℝ := ∏ i, psi (x i)
def tht (x : V m) : ℝ := ∏ i, rho (x i)
def vlat (n : Fin m → ℤ) : V m := WithLp.toLp 2 (fun i => (n i : ℝ) / 2)
def wlat (ξ : Fin m → ℤ) : V m := WithLp.toLp 2 (fun i => (ξ i : ℝ))

@[simp] lemma vlat_apply (n : Fin m → ℤ) (i : Fin m) : vlat n i = (n i : ℝ) / 2 := rfl
@[simp] lemma wlat_apply (n : Fin m → ℤ) (i : Fin m) : wlat n i = (n i : ℝ) := rfl

lemma coord_smooth (i : Fin m) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : V m => x i) :=
  (EuclideanSpace.proj i : V m →L[ℝ] ℝ).contDiff

lemma chi_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chi (m := m)) :=
  contDiff_prod fun i _ => psi_smooth.comp (coord_smooth i)

lemma tht_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tht (m := m)) :=
  contDiff_prod fun i _ => rho_smooth.comp (coord_smooth i)

lemma chi_supp {x : V m} (h : chi x ≠ 0) (i : Fin m) : |x i| < 3 / 8 := by
  by_contra h'
  apply h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (psi_zero (not_lt.1 h'))

lemma tht_one {x : V m} (h : ∀ i, |x i| ≤ 3 / 8) : tht x = 1 :=
  Finset.prod_eq_one fun i _ => rho_one (h i)

lemma tht_zero {x : V m} (i : Fin m) (h : 7 / 16 ≤ |x i|) : tht x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (rho_zero h)

lemma norm_le_of_coord {x : V m} (h : ∀ i, |x i| ≤ 1) : ‖x‖ ≤ m := by
  rw [EuclideanSpace.norm_eq]
  have h1 : ∑ i, ‖x i‖ ^ 2 ≤ (m : ℝ) ^ 2 := by
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs, sq_abs]; nlinarith [abs_nonneg (x i), h i, sq_abs (x i)]
      _ = m := by simp
      _ ≤ (m : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos m with hm | hm
          · simp [hm]
          · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
            nlinarith
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt ((m : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
    _ = m := Real.sqrt_sq (Nat.cast_nonneg _)

lemma chi_support_sub : Function.support (chi (m := m)) ⊆ Metric.closedBall 0 m := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  exact norm_le_of_coord fun i => by linarith [chi_supp hx i]

lemma tht_support_sub : Function.support (tht (m := m)) ⊆ Metric.closedBall 0 m := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  refine norm_le_of_coord fun i => ?_
  by_contra h'
  exact hx (tht_zero i (by linarith [not_le.1 h']))

lemma tsupport_chi_sub : tsupport (chi (m := m)) ⊆ Metric.closedBall 0 m :=
  closure_minimal chi_support_sub Metric.isClosed_closedBall

lemma tsupport_tht_sub : tsupport (tht (m := m)) ⊆ Metric.closedBall 0 m :=
  closure_minimal tht_support_sub Metric.isClosed_closedBall

lemma chi_cs : HasCompactSupport (chi (m := m)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 _) chi_support_sub

lemma tht_cs : HasCompactSupport (tht (m := m)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 _) tht_support_sub

lemma tht_chi {x : V m} (h : chi x ≠ 0) : tht x = 1 :=
  tht_one fun i => (chi_supp h i).le

lemma chi_hasSum (x : V m) : HasSum (fun n : Fin m → ℤ => chi (x - vlat n)) 1 := by
  classical
  let T : Fin m → Finset ℤ := fun i => Finset.Icc (⌊2 * x i⌋ - 2) (⌊2 * x i⌋ + 2)
  have hval : ∑ n ∈ Fintype.piFinset T, chi (x - vlat n) = 1 := by
    simp only [chi, PiLp.sub_apply, vlat_apply]
    rw [← Finset.prod_univ_sum (t := T) (f := fun i k => psi (x i - (k : ℝ) / 2))]
    exact Finset.prod_eq_one fun i _ => psi_sum_Icc (x i)
  rw [← hval]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  rw [Fintype.mem_piFinset, not_forall] at hn
  obtain ⟨i, hi⟩ := hn
  simp only [chi, PiLp.sub_apply, vlat_apply]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply psi_zero
  have h1 : ((⌊2 * x i⌋ : ℤ) : ℝ) ≤ 2 * x i := Int.floor_le _
  have h2 : 2 * x i < ⌊2 * x i⌋ + 1 := Int.lt_floor_add_one _
  simp only [T, Finset.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hk | hk
  · have : (n i : ℝ) ≤ ⌊2 * x i⌋ - 3 := by exact_mod_cast (by omega : n i ≤ ⌊2 * x i⌋ - 3)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (⌊2 * x i⌋ : ℝ) + 3 ≤ n i := by exact_mod_cast (by omega : ⌊2 * x i⌋ + 3 ≤ n i)
    rw [abs_of_neg (by linarith)]
    linarith

/-! ### Fourier series of functions supported in a small cube -/

section fs

/-- the additive character `t ↦ e^{2π i t}` -/
def ech (t : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * t) * Complex.I)

lemma ech_neg (t : ℝ) : ech (-t) = (starRingEnd ℂ) (ech t) := by
  rw [ech, ech, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma inner_wlat (y : V m) (ξ : Fin m → ℤ) : inner ℝ y (wlat ξ) = ∑ i, y i * ξ i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [wlat_apply, mul_comm]

lemma mFourier_coe (x : Fin m → ℝ) (ξ : Fin m → ℤ) :
    UnitAddTorus.mFourier ξ (fun i => (x i : UnitAddCircle)) =
      ech (inner ℝ (WithLp.toLp 2 x : V m) (wlat ξ)) := by
  rw [inner_wlat]
  change ∏ i : Fin m, fourier (ξ i) ((x i : UnitAddCircle)) = _
  rw [ech]
  rw [Finset.prod_congr rfl fun i _ => fourier_coe_apply (T := 1) (n := ξ i) (x := x i)]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  try simp only [WithLp.ofLp_toLp]
  push_cast
  ring

/-- representative in `(-1/2, 1/2]` -/
def rep (z : UnitAddCircle) : ℝ := (AddCircle.equivIoc 1 (-1 / 2) z : ℝ)

lemma rep_coe {t : ℝ} (ht : t ∈ Ioc (-1 / 2 : ℝ) (1 / 2)) : rep (t : UnitAddCircle) = t := by
  have ht' : t ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
    refine ⟨ht.1, ?_⟩; linarith [ht.2]
  simp [rep, AddCircle.equivIoc_coe_of_mem ht']

lemma coe_rep (z : UnitAddCircle) : ((rep z : ℝ) : UnitAddCircle) = z :=
  AddCircle.coe_equivIoc

/-- periodisation of a function supported in the cube `|y_i| < 3/8` -/
def per (h : V m → ℂ) (z : UnitAddTorus (Fin m)) : ℂ :=
  h (WithLp.toLp 2 (fun i => rep (z i)))

lemma per_coe (h : V m → ℂ) (x : Fin m → ℝ) (hx : ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (1 / 2)) :
    per h (fun i => (x i : UnitAddCircle)) = h (WithLp.toLp 2 x) := by
  simp only [per]
  congr 2
  funext i
  exact rep_coe (hx i)

lemma per_cont (h : V m → ℂ) (hc : Continuous h) (hsupp : ∀ y, h y ≠ 0 → ∀ i, |y i| < 3 / 8) :
    Continuous (per h) := by
  rw [continuous_iff_continuousAt]
  intro z0
  by_cases h0 : ∀ i, z0 i ≠ ((-1 / 2 : ℝ) : UnitAddCircle)
  · have hr : ContinuousAt (fun z : UnitAddTorus (Fin m) => (WithLp.toLp 2 (fun i => rep (z i)) : V m)) z0 := by
      have h1 : ContinuousAt (fun z : UnitAddTorus (Fin m) => (fun i => rep (z i))) z0 := by
        refine continuousAt_pi.2 fun i => ?_
        have h2 : ContinuousAt rep (z0 i) :=
          continuous_subtype_val.continuousAt.comp (AddCircle.continuousAt_equivIoc 1 (-1 / 2) (h0 i))
        exact h2.comp (f := fun z : UnitAddTorus (Fin m) => z i) (continuous_apply i).continuousAt
      exact (PiLp.continuous_toLp 2 _).continuousAt.comp h1
    exact hc.continuousAt.comp hr
  · push Not at h0
    obtain ⟨i, hi⟩ := h0
    let K : Set UnitAddCircle := (fun t : ℝ => (t : UnitAddCircle)) '' Icc (-3 / 8) (3 / 8)
    have hK : IsClosed K :=
      (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed
    have hz0K : z0 i ∉ K := by
      rintro ⟨t, ht, hteq⟩
      have hteq' : ((t : ℝ) : UnitAddCircle) = z0 i := hteq
      have e1 : rep (t : UnitAddCircle) = t := rep_coe ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have e2 : rep (((-1 / 2 : ℝ)) : UnitAddCircle) = 1 / 2 := by
        have : (((-1 / 2 : ℝ)) : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) := by
          rw [show (1 / 2 : ℝ) = -1 / 2 + 1 by norm_num, AddCircle.coe_add_period]
        rw [this, rep_coe ⟨by norm_num, le_rfl⟩]
      rw [hteq', hi] at e1
      rw [e1] at e2
      linarith [ht.2]
    have hzero : ∀ z : UnitAddTorus (Fin m), z i ∉ K → per h z = 0 := by
      intro z hz
      by_contra hne
      have := hsupp _ hne i
      apply hz
      refine ⟨rep (z i), ⟨?_, ?_⟩, coe_rep (z i)⟩ <;>
        · simp only [PiLp.toLp_apply] at this
          linarith [abs_lt.1 this]
    have hev : ∀ᶠ z in 𝓝 z0, per h z = 0 := by
      have : (fun z : UnitAddTorus (Fin m) => z i) ⁻¹' Kᶜ ∈ 𝓝 z0 :=
        (hK.isOpen_compl.preimage (continuous_apply i)).mem_nhds hz0K
      filter_upwards [this] with z hz
      exact hzero z hz
    rw [ContinuousAt, hzero z0 hz0K]
    exact tendsto_nhds_of_eventually_eq hev

lemma fchar_eq (t : ℝ) : ((𝐞 t : Circle) : ℂ) = ech t := rfl

lemma fourier_eq_ech (h : V m → ℂ) (w : V m) :
    𝓕 h w = ∫ v, ech (-inner ℝ v w) * h v := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul, fchar_eq]

lemma inner_wlat_neg (y : V m) (ξ : Fin m → ℤ) : inner ℝ y (wlat (-ξ)) = -inner ℝ y (wlat ξ) := by
  rw [inner_wlat, inner_wlat, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma per_coeff (h : V m → ℂ) (hsupp : ∀ y, h y ≠ 0 → ∀ i, |y i| < 3 / 8) (ξ : Fin m → ℤ) :
    UnitAddTorus.mFourierCoeff (per h) ξ = 𝓕 h (wlat ξ) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral (per h) ξ (fun _ => -1 / 2), fourier_eq_ech]
  let G : (Fin m → ℝ) → ℂ := fun x => ech (-inner ℝ (WithLp.toLp 2 x : V m) (wlat ξ)) * h (WithLp.toLp 2 x)
  have hS : MeasurableSet {x : Fin m → ℝ | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
      ((fun _ => (-1 / 2 : ℝ)) i + 1)} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => (measurable_pi_apply i) measurableSet_Ioc
  have e1 : ∫ x in {x : Fin m → ℝ | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
      ((fun _ => (-1 / 2 : ℝ)) i + 1)},
      UnitAddTorus.mFourier (-ξ) (fun i => (x i : UnitAddCircle)) • per h (fun i => (x i : UnitAddCircle)) =
      ∫ x in {x : Fin m → ℝ | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
      ((fun _ => (-1 / 2 : ℝ)) i + 1)}, G x := by
    refine setIntegral_congr_fun hS fun x hx => ?_
    have hx' : ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (1 / 2) := fun i =>
      ⟨(hx i).1, by have := (hx i).2; norm_num at this ⊢; linarith⟩
    simp only [G, smul_eq_mul, mFourier_coe, per_coe h x hx', inner_wlat_neg]
  have e2 : ∫ x in {x : Fin m → ℝ | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
      ((fun _ => (-1 / 2 : ℝ)) i + 1)}, G x = ∫ x, G x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    simp only [Set.mem_ofPred_eq, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    have : h (WithLp.toLp 2 x) = 0 := by
      by_contra hne
      have h1 := hsupp _ hne i
      simp only [WithLp.ofLp_toLp] at h1
      apply hi
      rw [abs_lt] at h1
      constructor <;> norm_num <;> linarith [h1.1, h1.2]
    simp [G, this]
  have e3 : ∫ x, G x = ∫ v : V m, ech (-inner ℝ v (wlat ξ)) * h v :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm.integral_comp'
      (fun v : V m => ech (-inner ℝ v (wlat ξ)) * h v)
  rw [e1, e2, e3]

theorem fs_hasSum (h : V m → ℂ) (hc : Continuous h) (hsupp : ∀ y, h y ≠ 0 → ∀ i, |y i| < 3 / 8)
    (hsum : Summable fun ξ : Fin m → ℤ => 𝓕 h (wlat ξ)) (y : V m) (hy : ∀ i, |y i| < 1 / 2) :
    HasSum (fun ξ => 𝓕 h (wlat ξ) * ech (inner ℝ y (wlat ξ))) (h y) := by
  let H : C(UnitAddTorus (Fin m), ℂ) := ⟨per h, per_cont h hc hsupp⟩
  have hcoef : ∀ ξ, UnitAddTorus.mFourierCoeff H ξ = 𝓕 h (wlat ξ) := per_coeff h hsupp
  have hs : Summable (UnitAddTorus.mFourierCoeff H) := by
    have e : UnitAddTorus.mFourierCoeff H = fun ξ => 𝓕 h (wlat ξ) := funext hcoef
    rw [e]; exact hsum
  have := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (fun i => ((y i : ℝ) : UnitAddCircle))
  have hy' : ∀ i, y i ∈ Ioc (-1 / 2 : ℝ) (1 / 2) := fun i =>
    ⟨by linarith [(abs_lt.1 (hy i)).1], by linarith [(abs_lt.1 (hy i)).2]⟩
  have hH : H (fun i => ((y i : ℝ) : UnitAddCircle)) = h y := by
    show per h _ = h y
    rw [per_coe h (fun i => y i) hy']
  rw [hH] at this
  convert this using 2 with ξ
  rw [hcoef, smul_eq_mul, mFourier_coe]

end fs

/-! ### Schwartz estimates for the coefficient functionals -/

section coef

abbrev Sch (m : ℕ) := SchwartzMap (V m) ℂ

def chiC (x : V m) : ℂ := (chi x : ℂ)
def thtC (x : V m) : ℂ := (tht x : ℂ)

lemma chiC_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chiC (m := m)) :=
  Complex.ofRealCLM.contDiff.comp chi_smooth

lemma thtC_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (thtC (m := m)) :=
  Complex.ofRealCLM.contDiff.comp tht_smooth

lemma chiC_cs : HasCompactSupport (chiC (m := m)) :=
  chi_cs.comp_left Complex.ofReal_zero

lemma thtC_cs : HasCompactSupport (thtC (m := m)) :=
  tht_cs.comp_left Complex.ofReal_zero

lemma tsupport_chiC : tsupport (chiC (m := m)) ⊆ Metric.closedBall 0 m :=
  (tsupport_comp_subset Complex.ofReal_zero _).trans tsupport_chi_sub

lemma tsupport_thtC : tsupport (thtC (m := m)) ⊆ Metric.closedBall 0 m :=
  (tsupport_comp_subset Complex.ofReal_zero _).trans tsupport_tht_sub

/-- uniform bound on the first `d` derivatives of a compactly supported smooth function -/
lemma cs_bound {g : V m → ℂ} (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hc : HasCompactSupport g)
    (d : ℕ) : ∃ M, 0 ≤ M ∧ ∀ i ≤ d, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ M := by
  have h : ∀ i, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ C := fun i =>
    (hs.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hc.iteratedFDeriv i)
  choose C hC using h
  refine ⟨∑ i ∈ Finset.range (d + 1), max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    fun i hi x => ?_⟩
  calc ‖iteratedFDeriv ℝ i g x‖ ≤ max (C i) 0 := (hC i x).trans (le_max_left _ _)
    _ ≤ ∑ i ∈ Finset.range (d + 1), max (C i) 0 :=
        Finset.single_le_sum (f := fun i => max (C i) 0) (fun j _ => le_max_right _ _)
          (Finset.mem_range.2 (by omega))

lemma leib {a g : V m → ℂ} (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : V m) {d : ℕ} {M B : ℝ}
    (hM : ∀ i ≤ d, ‖iteratedFDeriv ℝ i a x‖ ≤ M) (hB : ∀ j ≤ d, ‖iteratedFDeriv ℝ j g x‖ ≤ B)
    (h0M : 0 ≤ M) (h0B : 0 ≤ B) :
    ‖iteratedFDeriv ℝ d (fun y => a y * g y) x‖ ≤ 2 ^ d * M * B := by
  refine (norm_iteratedFDeriv_mul_le ha hg x (by exact_mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * ‖iteratedFDeriv ℝ i a x‖ *
        ‖iteratedFDeriv ℝ (d - i) g x‖
      ≤ ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * M * B := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ d := by rw [Finset.mem_range] at hi; omega
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hM i hi') (Nat.cast_nonneg _))
          (hB (d - i) (by omega)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) h0M)
    _ = 2 ^ d * M * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose d

lemma one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (A : ℕ) : (1 + t) ^ A ≤ 2 ^ A * (1 + t ^ A) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ A ≤ 2 ^ A := pow_le_pow_left₀ (by linarith) (by linarith) A
      _ ≤ 2 ^ A * (1 + t ^ A) := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (by positivity))
  · calc (1 + t) ^ A ≤ (2 * t) ^ A := pow_le_pow_left₀ (by linarith) (by linarith) A
      _ = 2 ^ A * t ^ A := mul_pow _ _ _
      _ ≤ 2 ^ A * (1 + t ^ A) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- the seminorm `max_{k ≤ A, n ≤ d} p_{k,n}` -/
def Qs (A d : ℕ) : Seminorm ℂ (Sch m) :=
  (Finset.range (A + 1) ×ˢ Finset.range (d + 1)).sup (schwartzSeminormFamily ℂ (V m) ℂ)

lemma Qs_cont (A d : ℕ) : Continuous (Qs (m := m) A d) :=
  (schwartz_withSeminorms ℂ (V m) ℂ).finset_sups.continuous_seminorm _

lemma le_Qs {A d k n : ℕ} (hk : k ≤ A) (hn : n ≤ d) (f : Sch m) :
    SchwartzMap.seminorm ℂ k n f ≤ Qs A d f := by
  have hmem : ((k, n) : ℕ × ℕ) ∈ Finset.range (A + 1) ×ˢ Finset.range (d + 1) :=
    Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  exact Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (V m) ℂ) hmem

lemma pw_bound {A d j : ℕ} (hj : j ≤ d) (f : Sch m) (y : V m) :
    (1 + ‖y‖) ^ A * ‖iteratedFDeriv ℝ j f y‖ ≤ 2 ^ (A + 1) * Qs A d f := by
  have h1 := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f j y
  have h2 := SchwartzMap.le_seminorm ℂ A j f y
  have h3 := le_Qs (m := m) (A := A) (d := d) (k := 0) (n := j) (Nat.zero_le _) hj f
  have h4 := le_Qs (m := m) (A := A) (d := d) (k := A) (n := j) le_rfl hj f
  have h5 := one_add_pow_le ‖y‖ (norm_nonneg _) A
  calc (1 + ‖y‖) ^ A * ‖iteratedFDeriv ℝ j f y‖
      ≤ 2 ^ A * (1 + ‖y‖ ^ A) * ‖iteratedFDeriv ℝ j f y‖ :=
        mul_le_mul_of_nonneg_right h5 (norm_nonneg _)
    _ = 2 ^ A * (‖iteratedFDeriv ℝ j f y‖ + ‖y‖ ^ A * ‖iteratedFDeriv ℝ j f y‖) := by ring
    _ ≤ 2 ^ A * (Qs A d f + Qs A d f) := by gcongr <;> linarith
    _ = 2 ^ (A + 1) * Qs A d f := by ring

/-- decay of the Fourier transform -/
lemma ft_bound (A : ℕ) : ∃ q : Seminorm ℂ (Sch m), Continuous q ∧
    ∀ (g : Sch m) (w : V m), (1 + ‖w‖) ^ A * ‖𝓕 (g : V m → ℂ) w‖ ≤ q g := by
  let F := SchwartzMap.fourierTransformCLM ℂ (E := ℂ) (V := V m)
  refine ⟨((2 : NNReal) ^ (A + 1)) • (Qs A 0).comp (F : Sch m →ₗ[ℂ] Sch m), ?_, fun g w => ?_⟩
  · have : Continuous fun g : Sch m => Qs A 0 (F g) := (Qs_cont A 0).comp F.continuous
    have h2 := this.const_smul ((2 : NNReal) ^ (A + 1))
    rw [FunLike.coe_smul]
    exact h2
  · have h := pw_bound (A := A) (d := 0) (j := 0) le_rfl (F g) w
    rw [norm_iteratedFDeriv_zero] at h
    rw [smul_apply, NNReal.smul_def, smul_eq_mul]
    push_cast
    exact h

/-- the cut-off translate `y ↦ χ(y) f(y + v)` -/
def hS (v : V m) : Sch m →L[ℂ] Sch m :=
  (SchwartzMap.smulLeftCLM ℂ (chiC (m := m))) ∘L (SchwartzMap.compSubConstCLM ℂ (-v))

lemma hS_apply (v : V m) (f : Sch m) (y : V m) : hS v f y = chiC y * f (y + v) := by
  simp only [hS, ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply (chiC_cs.hasTemperateGrowth chiC_smooth),
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul]

lemma hS_coe (v : V m) (f : Sch m) : (hS v f : V m → ℂ) = fun y => chiC y * f (y + v) :=
  funext (hS_apply v f)

lemma hS_bound (A K : ℕ) : ∃ C, 0 ≤ C ∧ ∀ (v : V m) (f : Sch m),
    (1 + ‖v‖) ^ A * Qs K K (hS v f) ≤ C * Qs A K f := by
  obtain ⟨M, hM0, hM⟩ := cs_bound (chiC_smooth (m := m)) chiC_cs K
  refine ⟨(1 + m) ^ K * 2 ^ K * M * 2 ^ (A + 1) * (1 + m) ^ A, by positivity, fun v f => ?_⟩
  have hv : 0 < (1 + ‖v‖) ^ A := by positivity
  rw [← le_div_iff₀' hv]
  refine Seminorm.finset_sup_apply_le (by positivity) fun kd hkd => ?_
  obtain ⟨hk, hd⟩ := Finset.mem_product.1 hkd
  rw [Finset.mem_range] at hk hd
  refine SchwartzMap.seminorm_le_bound ℂ kd.1 kd.2 _ (by positivity) fun x => ?_
  by_cases hx : x ∈ tsupport (chiC (m := m))
  · have hxm : ‖x‖ ≤ m := mem_closedBall_zero_iff.1 (tsupport_chiC hx)
    have hB : ∀ j ≤ kd.2, ‖iteratedFDeriv ℝ j (fun y => f (y + v)) x‖ ≤
        2 ^ (A + 1) * (1 + m) ^ A * Qs A K f / (1 + ‖v‖) ^ A := by
      intro j hj
      rw [iteratedFDeriv_comp_add_right]
      rw [le_div_iff₀' hv]
      have h1 := pw_bound (A := A) (d := K) (j := j) (by omega) f (x + v)
      have h2 : (1 + ‖v‖) ^ A ≤ (1 + m) ^ A * (1 + ‖x + v‖) ^ A := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ A
        have : ‖v‖ ≤ ‖x + v‖ + ‖x‖ := by
          calc ‖v‖ = ‖(x + v) - x‖ := by rw [add_sub_cancel_left]
            _ ≤ ‖x + v‖ + ‖x‖ := norm_sub_le _ _
        nlinarith [norm_nonneg (x + v), norm_nonneg x]
      calc (1 + ‖v‖) ^ A * ‖iteratedFDeriv ℝ j f (x + v)‖
          ≤ (1 + m) ^ A * (1 + ‖x + v‖) ^ A * ‖iteratedFDeriv ℝ j f (x + v)‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = (1 + m) ^ A * ((1 + ‖x + v‖) ^ A * ‖iteratedFDeriv ℝ j f (x + v)‖) := by ring
        _ ≤ (1 + m) ^ A * (2 ^ (A + 1) * Qs A K f) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 ^ (A + 1) * (1 + m) ^ A * Qs A K f := by ring
    have hL := leib chiC_smooth ((f.smooth ⊤).comp (contDiff_id.add contDiff_const)) x
      (d := kd.2) (M := M) (fun i hi => hM i (by omega) x) hB hM0 (by positivity)
    rw [hS_coe]
    have hxk : ‖x‖ ^ kd.1 ≤ (1 + m) ^ K := by
      calc ‖x‖ ^ kd.1 ≤ (1 + m) ^ kd.1 := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        _ ≤ (1 + m) ^ K := pow_le_pow_right₀ (by linarith) (by omega)
    have h2d : (2 : ℝ) ^ kd.2 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
    calc ‖x‖ ^ kd.1 * ‖iteratedFDeriv ℝ kd.2 (fun y => chiC y * f (y + v)) x‖
        ≤ (1 + m) ^ K * (2 ^ K * M * (2 ^ (A + 1) * (1 + m) ^ A * Qs A K f / (1 + ‖v‖) ^ A)) := by
          refine mul_le_mul hxk (hL.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = (1 + m) ^ K * 2 ^ K * M * 2 ^ (A + 1) * (1 + m) ^ A * Qs A K f / (1 + ‖v‖) ^ A := by ring
  · have hz : iteratedFDeriv ℝ kd.2 (hS v f : V m → ℂ) x = 0 := by
      have hsub : tsupport (hS v f : V m → ℂ) ⊆ tsupport (chiC (m := m)) := by
        rw [hS_coe]; exact tsupport_mul_subset_left
      by_contra hne
      exact hx (hsub (support_iteratedFDeriv_subset kd.2 hne))
    rw [hz, norm_zero, mul_zero]
    positivity

/-- the coefficient functional `f ↦ 𝓕(χ · f(· + v_n))(w_ξ)` -/
def phiF (n ξ : Fin m → ℤ) : StrongDual ℂ (Sch m) :=
  (BoundedContinuousFunction.evalCLM ℂ (wlat ξ)) ∘L (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (V m) ℂ) ∘L
    (SchwartzMap.fourierTransformCLM ℂ) ∘L hS (vlat n)

lemma phiF_apply (n ξ : Fin m → ℤ) (f : Sch m) :
    phiF n ξ f = 𝓕 (fun y => chiC y * f (y + vlat n)) (wlat ξ) := by
  simp only [phiF, ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
    SchwartzMap.toBoundedContinuousFunctionCLM_apply, SchwartzMap.fourierTransformCLM_apply]
  rw [SchwartzMap.fourier_coe, hS_coe]

lemma phiF_decay (A : ℕ) : ∃ q : Seminorm ℂ (Sch m), Continuous q ∧ ∀ (n ξ : Fin m → ℤ) (f : Sch m),
    (1 + ‖wlat ξ‖) ^ A * (1 + ‖vlat n‖) ^ A * ‖phiF n ξ f‖ ≤ q f := by
  obtain ⟨q, hq, hqb⟩ := ft_bound (m := m) A
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (V m) ℂ) q hq
  let K := s.sup fun i => i.1 + i.2
  have hsK : ∀ g : Sch m, (s.sup (schwartzSeminormFamily ℂ (V m) ℂ)) g ≤ Qs K K g := by
    intro g
    refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => ?_
    have : i.1 + i.2 ≤ K := Finset.le_sup (f := fun i : ℕ × ℕ => i.1 + i.2) hi
    exact le_Qs (by omega) (by omega) g
  obtain ⟨C', hC'0, hC'⟩ := hS_bound (m := m) A K
  refine ⟨((C : NNReal) * C'.toNNReal) • Qs A K, ?_, fun n ξ f => ?_⟩
  · rw [FunLike.coe_smul]; exact (Qs_cont A K).const_smul _
  · have h1 := hqb (hS (vlat n) f) (wlat ξ)
    have e : ‖phiF n ξ f‖ = ‖𝓕 (hS (vlat n) f : V m → ℂ) (wlat ξ)‖ := by
      rw [phiF_apply, hS_coe]
    have h2 := hC (hS (vlat n) f)
    have h3 := hsK (hS (vlat n) f)
    have h4 := hC' (vlat n) f
    rw [smul_apply, NNReal.smul_def, smul_eq_mul, NNReal.coe_mul,
      Real.coe_toNNReal _ hC'0]
    rw [smul_apply, NNReal.smul_def, smul_eq_mul] at h2
    have hv : 0 ≤ (1 + ‖vlat n‖) ^ A := by positivity
    calc (1 + ‖wlat ξ‖) ^ A * (1 + ‖vlat n‖) ^ A * ‖phiF n ξ f‖
        = (1 + ‖vlat n‖) ^ A * ((1 + ‖wlat ξ‖) ^ A * ‖𝓕 (hS (vlat n) f : V m → ℂ) (wlat ξ)‖) := by
          rw [e]; ring
      _ ≤ (1 + ‖vlat n‖) ^ A * (C * Qs K K (hS (vlat n) f)) := by
          refine mul_le_mul_of_nonneg_left (h1.trans (h2.trans ?_)) hv
          exact mul_le_mul_of_nonneg_left h3 C.2
      _ = C * ((1 + ‖vlat n‖) ^ A * Qs K K (hS (vlat n) f)) := by ring
      _ ≤ C * (C' * Qs A K f) := mul_le_mul_of_nonneg_left h4 C.2
      _ = C * C' * Qs A K f := by ring

end coef

/-! ### the frame vectors -/

section vec

lemma ech_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ech :=
  Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
    contDiff_const)

lemma ech_hasDerivAt (t : ℝ) : HasDerivAt ech (2 * Real.pi * Complex.I * ech t) t :=
  Real.hasDerivAt_fourierChar t

lemma ech_iter (j : ℕ) : iteratedDeriv j ech = fun t => (2 * Real.pi * Complex.I) ^ j * ech t := by
  induction j with
  | zero => funext t; simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [((ech_hasDerivAt t).const_mul ((2 * Real.pi * Complex.I) ^ j)).deriv]
    ring

lemma norm_ech (t : ℝ) : ‖ech t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma ech_deriv_norm (j : ℕ) (t : ℝ) : ‖iteratedFDeriv ℝ j ech t‖ = (2 * Real.pi) ^ j := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ech_iter, norm_mul, norm_ech, mul_one, norm_pow]
  congr 1
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

lemma char_eq (w : V m) : (fun x : V m => ech (inner ℝ x w)) = ech ∘ (innerSL ℝ w) := by
  funext x
  simp [real_inner_comm]

lemma char_smooth (w : V m) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : V m => ech (inner ℝ x w)) := by
  rw [char_eq]; exact ech_smooth.comp (innerSL ℝ w).contDiff

lemma char_bound (w : V m) (j : ℕ) (x : V m) :
    ‖iteratedFDeriv ℝ j (fun x : V m => ech (inner ℝ x w)) x‖ ≤ (2 * Real.pi * ‖w‖) ^ j := by
  rw [char_eq, ContinuousLinearMap.iteratedFDeriv_comp_right (innerSL ℝ w) ech_smooth x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [ech_deriv_norm, Finset.prod_const, Finset.card_univ, Fintype.card_fin, innerSL_apply_norm,
    ← mul_pow]

def Gfun (ξ : Fin m → ℤ) (x : V m) : ℂ := thtC x * ech (inner ℝ x (wlat ξ))

lemma Gfun_smooth (ξ : Fin m → ℤ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gfun (m := m) ξ) :=
  thtC_smooth.mul (char_smooth _)

lemma Gfun_cs (ξ : Fin m → ℤ) : HasCompactSupport (Gfun (m := m) ξ) :=
  thtC_cs.mul_right

def Gs (ξ : Fin m → ℤ) : Sch m := (Gfun_cs ξ).toSchwartzMap (Gfun_smooth ξ)

/-- the frame vector `x ↦ θ(x - v_n) e^{2π i ⟨x - v_n, ξ⟩}` -/
def eF (n ξ : Fin m → ℤ) : Sch m := SchwartzMap.compSubConstCLM ℂ (vlat n) (Gs ξ)

lemma eF_apply (n ξ : Fin m → ℤ) (x : V m) :
    eF n ξ x = thtC (x - vlat n) * ech (inner ℝ (x - vlat n) (wlat ξ)) := rfl

lemma eF_growth (K : ℕ) : ∃ C, 0 ≤ C ∧ ∀ n ξ : Fin m → ℤ,
    Qs K K (eF n ξ) ≤ C * ((1 + ‖vlat n‖) ^ K * (1 + ‖wlat ξ‖) ^ K) := by
  obtain ⟨M, hM0, hM⟩ := cs_bound (thtC_smooth (m := m)) thtC_cs K
  refine ⟨(1 + m) ^ K * 2 ^ K * M * (2 * Real.pi) ^ K, by positivity, fun n ξ => ?_⟩
  refine Seminorm.finset_sup_apply_le (by positivity) fun kd hkd => ?_
  obtain ⟨hk, hd⟩ := Finset.mem_product.1 hkd
  rw [Finset.mem_range] at hk hd
  refine SchwartzMap.seminorm_le_bound ℂ kd.1 kd.2 _ (by positivity) fun x => ?_
  have hco : (eF n ξ : V m → ℂ) = fun x => Gfun ξ (x - vlat n) := rfl
  rw [hco, iteratedFDeriv_comp_sub]
  by_cases hx : x - vlat n ∈ tsupport (thtC (m := m))
  · have hxm : ‖x - vlat n‖ ≤ m := mem_closedBall_zero_iff.1 (tsupport_thtC hx)
    have hB : ∀ j ≤ kd.2, ‖iteratedFDeriv ℝ j (fun x : V m => ech (inner ℝ x (wlat ξ))) (x - vlat n)‖ ≤
        (2 * Real.pi) ^ K * (1 + ‖wlat ξ‖) ^ K := by
      intro j hj
      refine (char_bound _ j _).trans ?_
      rw [mul_pow]
      have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      refine mul_le_mul (pow_le_pow_right₀ hpi (by omega)) ?_ (by positivity) (by positivity)
      calc ‖wlat ξ‖ ^ j ≤ (1 + ‖wlat ξ‖) ^ j := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        _ ≤ (1 + ‖wlat ξ‖) ^ K := pow_le_pow_right₀ (by linarith [norm_nonneg (wlat ξ)]) (by omega)
    have hL := leib thtC_smooth (char_smooth (wlat ξ)) (x - vlat n) (d := kd.2) (M := M)
      (fun i hi => hM i (by omega) _) hB hM0 (by positivity)
    have hxk : ‖x‖ ^ kd.1 ≤ (1 + m) ^ K * (1 + ‖vlat n‖) ^ K := by
      rw [← mul_pow]
      have h1 : ‖x‖ ≤ ‖x - vlat n‖ + ‖vlat n‖ := by
        calc ‖x‖ = ‖(x - vlat n) + vlat n‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖x‖ ≤ (1 + m) * (1 + ‖vlat n‖) := by nlinarith [norm_nonneg (vlat n)]
      calc ‖x‖ ^ kd.1 ≤ ((1 + m) * (1 + ‖vlat n‖)) ^ kd.1 := pow_le_pow_left₀ (norm_nonneg _) h2 _
        _ ≤ ((1 + m) * (1 + ‖vlat n‖)) ^ K := by
            refine pow_le_pow_right₀ ?_ (by omega)
            nlinarith [norm_nonneg (vlat n)]
    have h2d : (2 : ℝ) ^ kd.2 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
    have hG : (Gfun ξ : V m → ℂ) = fun y => thtC y * ech (inner ℝ y (wlat ξ)) := rfl
    rw [hG]
    calc ‖x‖ ^ kd.1 * ‖iteratedFDeriv ℝ kd.2 (fun y => thtC y * ech (inner ℝ y (wlat ξ))) (x - vlat n)‖
        ≤ ((1 + m) ^ K * (1 + ‖vlat n‖) ^ K) * (2 ^ K * M * ((2 * Real.pi) ^ K * (1 + ‖wlat ξ‖) ^ K)) := by
          refine mul_le_mul hxk (hL.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = (1 + m) ^ K * 2 ^ K * M * (2 * Real.pi) ^ K * ((1 + ‖vlat n‖) ^ K * (1 + ‖wlat ξ‖) ^ K) := by
          ring
  · have hz : iteratedFDeriv ℝ kd.2 (Gfun (m := m) ξ) (x - vlat n) = 0 := by
      have hsub : tsupport (Gfun (m := m) ξ) ⊆ tsupport (thtC (m := m)) := tsupport_mul_subset_left
      by_contra hne
      exact hx (hsub (support_iteratedFDeriv_subset kd.2 hne))
    rw [hz, norm_zero, mul_zero]
    positivity

end vec

/-! ### weights and the nuclear domination of the frame -/

section dom

def gw (k : ℤ) : ℝ := ((1 + |(k : ℝ)| / 2) ^ 2)⁻¹

lemma gw_nonneg (k : ℤ) : 0 ≤ gw k := by unfold gw; positivity

lemma gw_summable : Summable gw := by
  have h := (Real.summable_one_div_int_add_rpow (1 / 2) 2).2 (by norm_num)
  refine Summable.of_nonneg_of_le gw_nonneg (fun k => ?_) (h.mul_left 4)
  have hk : 0 < |(k : ℝ) + 1 / 2| := by
    rw [abs_pos]
    intro h0
    have : (2 * k + 1 : ℝ) = 0 := by linarith
    have : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast this
    omega
  rw [gw, Real.rpow_two, one_div, ← div_eq_mul_inv]
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |(k : ℝ) + 1 / 2| ≤ |(k : ℝ)| + 1 / 2 := by
    calc |(k : ℝ) + 1 / 2| ≤ |(k : ℝ)| + |(1 / 2 : ℝ)| := abs_add_le _ _
      _ = |(k : ℝ)| + 1 / 2 := by norm_num
  have h2 : 0 ≤ |(k : ℝ) + 1 / 2| := abs_nonneg _
  nlinarith [abs_nonneg (k : ℝ)]

lemma prod_summable {g : ℤ → ℝ} (h0 : ∀ k, 0 ≤ g k) (hs : Summable g) :
    Summable (fun n : Fin m → ℤ => ∏ i, g (n i)) := by
  classical
  refine summable_of_sum_le (c := (∑' k, g k) ^ m) (fun n => Finset.prod_nonneg fun i _ => h0 _)
    fun s => ?_
  let T : Fin m → Finset ℤ := fun i => s.image (fun n => n i)
  have hsub : s ⊆ Fintype.piFinset T := fun n hn => Fintype.mem_piFinset.2 fun i =>
    Finset.mem_image.2 ⟨n, hn, rfl⟩
  calc ∑ n ∈ s, ∏ i, g (n i) ≤ ∑ n ∈ Fintype.piFinset T, ∏ i, g (n i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => Finset.prod_nonneg fun i _ => h0 _
    _ = ∏ i, ∑ k ∈ T i, g k := (Finset.prod_univ_sum T fun _ k => g k).symm
    _ ≤ ∏ _i : Fin m, ∑' k, g k := Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun k _ => h0 k)
        fun i _ => hs.sum_le_tsum _ fun k _ => h0 k
    _ = (∑' k, g k) ^ m := by simp

lemma weight_le (x : V m) (n : Fin m → ℤ) (hn : ∀ i, |(n i : ℝ)| / 2 ≤ |x i|) :
    ((1 + ‖x‖) ^ (2 * m))⁻¹ ≤ ∏ i, gw (n i) := by
  simp only [gw]
  rw [Finset.prod_inv_distrib]
  refine inv_anti₀ (Finset.prod_pos fun i _ => by positivity) ?_
  calc ∏ i, (1 + |(n i : ℝ)| / 2) ^ 2 ≤ ∏ _i : Fin m, (1 + ‖x‖) ^ 2 := by
        refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        have := PiLp.norm_apply_le x i
        rw [Real.norm_eq_abs] at this
        linarith [hn i]
    _ = (1 + ‖x‖) ^ (2 * m) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

/-- the weights of the frame -/
def cw (j : (Fin m → ℤ) × (Fin m → ℤ)) : ℝ :=
  ((1 + ‖vlat j.1‖) ^ (2 * m))⁻¹ * ((1 + ‖wlat j.2‖) ^ (2 * m))⁻¹

lemma cw_pos (j : (Fin m → ℤ) × (Fin m → ℤ)) : 0 < cw j := by unfold cw; positivity

lemma cw_summable : Summable (cw (m := m)) := by
  have ha : Summable fun n : Fin m → ℤ => ((1 + ‖vlat n‖) ^ (2 * m))⁻¹ :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => weight_le (vlat n) n fun i => by
        rw [vlat_apply, abs_div, abs_two])
      (prod_summable gw_nonneg gw_summable)
  have hb : Summable fun n : Fin m → ℤ => ((1 + ‖wlat n‖) ^ (2 * m))⁻¹ :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => weight_le (wlat n) n fun i => by
        rw [wlat_apply]; linarith [abs_nonneg (n i : ℝ)])
      (prod_summable gw_nonneg gw_summable)
  exact ha.mul_of_nonneg hb (fun n => by positivity) (fun n => by positivity)

lemma frame_dom (P : Seminorm ℂ (Sch m)) (hP : Continuous P) :
    ∃ P' : Seminorm ℂ (Sch m), Continuous P' ∧ ∀ (j : (Fin m → ℤ) × (Fin m → ℤ)) (f : Sch m),
      P (eF j.1 j.2) * ‖phiF j.1 j.2 f‖ ≤ cw j * P' f := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (V m) ℂ) P hP
  let K := s.sup fun i => i.1 + i.2
  have hsK : ∀ g : Sch m, (s.sup (schwartzSeminormFamily ℂ (V m) ℂ)) g ≤ Qs K K g := by
    intro g
    refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => ?_
    have : i.1 + i.2 ≤ K := Finset.le_sup (f := fun i : ℕ × ℕ => i.1 + i.2) hi
    exact le_Qs (by omega) (by omega) g
  obtain ⟨C1, hC10, hC1⟩ := eF_growth (m := m) K
  obtain ⟨q, hq, hqb⟩ := phiF_decay (m := m) (K + 2 * m)
  refine ⟨((C : NNReal) * C1.toNNReal) • q, ?_, fun j f => ?_⟩
  · rw [FunLike.coe_smul]; exact hq.const_smul _
  · rw [smul_apply, NNReal.smul_def, smul_eq_mul, NNReal.coe_mul, Real.coe_toNNReal _ hC10]
    have h1 : P (eF j.1 j.2) ≤ C * (C1 * ((1 + ‖vlat j.1‖) ^ K * (1 + ‖wlat j.2‖) ^ K)) := by
      have := hC (eF j.1 j.2)
      rw [smul_apply, NNReal.smul_def, smul_eq_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_left ((hsK _).trans (hC1 j.1 j.2)) C.2)
    have h2 := hqb j.1 j.2 f
    set a := 1 + ‖vlat j.1‖
    set b := 1 + ‖wlat j.2‖
    have ha : 0 < a := by positivity
    have hb : 0 < b := by positivity
    have e : cw j = (a ^ (2 * m))⁻¹ * (b ^ (2 * m))⁻¹ := rfl
    rw [e]
    have hφ := norm_nonneg (phiF j.1 j.2 f)
    calc P (eF j.1 j.2) * ‖phiF j.1 j.2 f‖
        ≤ C * (C1 * (a ^ K * b ^ K)) * ‖phiF j.1 j.2 f‖ := mul_le_mul_of_nonneg_right h1 hφ
      _ = C * C1 * ((a ^ (2 * m))⁻¹ * (b ^ (2 * m))⁻¹) *
            (b ^ (K + 2 * m) * a ^ (K + 2 * m) * ‖phiF j.1 j.2 f‖) := by
          rw [pow_add, pow_add]
          field_simp
      _ ≤ C * C1 * ((a ^ (2 * m))⁻¹ * (b ^ (2 * m))⁻¹) * q f :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (a ^ (2 * m))⁻¹ * (b ^ (2 * m))⁻¹ * (C * C1 * q f) := by ring

end dom

/-! ### completeness of the Schwartz space -/

section complete

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

lemma sch_sub_iter (f g : SchwartzMap E F) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n (f - g : SchwartzMap E F) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x := by
  have e : ((f - g : SchwartzMap E F) : E → F) = (f : E → F) - g := rfl
  rw [e]
  exact iteratedFDeriv_sub_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
    ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt

lemma cauchy_sn {𝓛 : Filter (SchwartzMap E F)} (h : Cauchy 𝓛) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ 𝓛, ∀ f ∈ A, ∀ g ∈ A, SchwartzMap.seminorm ℝ k n (f - g) < ε := by
  have hc : Continuous (SchwartzMap.seminorm ℝ k n : SchwartzMap E F → ℝ) :=
    (schwartz_withSeminorms ℝ E F).continuous_seminorm (k, n)
  have hU : (fun p : SchwartzMap E F × SchwartzMap E F => p.2 - p.1) ⁻¹'
      (SchwartzMap.seminorm ℝ k n).ball 0 ε ∈ uniformity (SchwartzMap E F) := by
    rw [uniformity_eq_comap_nhds_zero]
    exact preimage_mem_comap (Seminorm.ball_mem_nhds hc hε)
  obtain ⟨A, hA, hAA⟩ := (cauchy_iff.1 h).2 _ hU
  refine ⟨A, hA, fun f hf g hg => ?_⟩
  have := hAA (Set.mk_mem_prod hg hf)
  simp only [Set.mem_preimage, Seminorm.mem_ball_zero] at this
  exact this

instance sch_complete : CompleteSpace (SchwartzMap E F) := by
  refine ⟨fun {𝓛} h => ?_⟩
  have hne : 𝓛.NeBot := h.1
  -- pointwise limits of all derivatives
  have hlim : ∀ (n : ℕ) (x : E), ∃ D, Tendsto (fun f : SchwartzMap E F => iteratedFDeriv ℝ n f x) 𝓛 (𝓝 D) := by
    intro n x
    apply cauchy_iff_exists_le_nhds.1
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨A, hA, hAA⟩ := cauchy_sn h 0 n hε
    refine ⟨_, image_mem_map hA, ?_⟩
    rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
    rw [dist_eq_norm, ← sch_sub_iter]
    have := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (f - g) n x
    exact lt_of_le_of_lt this (hAA f hf g hg)
  choose D hD using hlim
  -- uniform weighted estimate
  have hunif : ∀ (k n : ℕ) (ε : ℝ), 0 < ε → ∃ A ∈ 𝓛, ∀ f ∈ A, ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x - D n x‖ ≤ ε := by
    intro k n ε hε
    obtain ⟨A, hA, hAA⟩ := cauchy_sn h k n hε
    refine ⟨A, hA, fun f hf x => ?_⟩
    have ht : Tendsto (fun g : SchwartzMap E F => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x‖)
        𝓛 (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x - D n x‖)) :=
      ((tendsto_const_nhds.sub (hD n x)).norm).const_mul _
    refine le_of_tendsto ht ?_
    filter_upwards [hA] with g hg
    rw [← sch_sub_iter]
    exact (SchwartzMap.le_seminorm ℝ k n (f - g) x).trans (hAA f hf g hg).le
  have hTU : ∀ n, TendstoUniformly (fun (f : SchwartzMap E F) x => iteratedFDeriv ℝ n f x) (D n) 𝓛 := by
    intro n
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨A, hA, hAA⟩ := hunif 0 n (ε / 2) (half_pos hε)
    filter_upwards [hA] with f hf x
    have := hAA f hf x
    rw [pow_zero, one_mul] at this
    rw [dist_comm, dist_eq_norm]
    linarith
  -- derivative relation
  have hder : ∀ n x, HasFDerivAt (D n)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F (D (n + 1) x)) x := by
    intro n
    let Ψ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F
    have hU : TendstoUniformly (fun (f : SchwartzMap E F) x => Ψ (iteratedFDeriv ℝ (n + 1) f x))
        (fun x => Ψ (D (n + 1) x)) 𝓛 :=
      Ψ.isometry.uniformContinuous.comp_tendstoUniformly (hTU (n + 1))
    refine hasFDerivAt_of_tendstoUniformly hU (fun f x => ?_) (fun x => hD n x)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (f : E → F)) :=
      (f.smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
    have e : Ψ (iteratedFDeriv ℝ (n + 1) f x) = fderiv ℝ (iteratedFDeriv ℝ n f) x := by
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
    rw [e]
    exact (hdiff x).hasFDerivAt
  -- the limit function
  have hlim0 : ∀ x, ∃ G, Tendsto (fun f : SchwartzMap E F => f x) 𝓛 (𝓝 G) := fun x =>
    ⟨(continuousMultilinearCurryFin0 ℝ E F) (D 0 x), by
      have := ((continuousMultilinearCurryFin0 ℝ E F).continuous.tendsto _).comp (hD 0 x)
      refine this.congr fun f => ?_
      simp [Function.comp_apply, iteratedFDeriv_zero_eq_comp]⟩
  choose G hG using hlim0
  have hit : ∀ n, iteratedFDeriv ℝ n G = D n := by
    intro n
    induction n with
    | zero =>
      rw [iteratedFDeriv_zero_eq_comp]
      funext x
      refine tendsto_nhds_unique ?_ (hD 0 x)
      have := ((continuousMultilinearCurryFin0 ℝ E F).symm.continuous.tendsto _).comp (hG x)
      refine this.congr fun f => ?_
      simp [Function.comp_apply, iteratedFDeriv_zero_eq_comp]
    | succ n ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, ih]
      funext x
      rw [Function.comp_apply, (hder n x).fderiv, LinearIsometryEquiv.symm_apply_apply]
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    refine contDiff_of_differentiable_iteratedFDeriv fun n _ => ?_
    rw [hit n]
    exact fun x => (hder n x).differentiableAt
  have hdecay : ∀ k n : ℕ, ∃ C, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n G x‖ ≤ C := by
    intro k n
    obtain ⟨A, hA, hAA⟩ := hunif k n 1 one_pos
    obtain ⟨f0, hf0⟩ := Filter.nonempty_of_mem hA
    refine ⟨SchwartzMap.seminorm ℝ k n f0 + 1, fun x => ?_⟩
    rw [hit n]
    have h1 := SchwartzMap.le_seminorm ℝ k n f0 x
    have h2 := hAA f0 hf0 x
    have h3 : ‖D n x‖ ≤ ‖iteratedFDeriv ℝ n f0 x‖ + ‖iteratedFDeriv ℝ n f0 x - D n x‖ := by
      calc ‖D n x‖ = ‖iteratedFDeriv ℝ n f0 x - (iteratedFDeriv ℝ n f0 x - D n x)‖ := by abel_nf
        _ ≤ _ := norm_sub_le _ _
    calc ‖x‖ ^ k * ‖D n x‖ ≤ ‖x‖ ^ k * (‖iteratedFDeriv ℝ n f0 x‖ + ‖iteratedFDeriv ℝ n f0 x - D n x‖) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ SchwartzMap.seminorm ℝ k n f0 + 1 := by rw [mul_add]; linarith
  let g : SchwartzMap E F := ⟨G, hsmooth, hdecay⟩
  refine ⟨g, ?_⟩
  show Tendsto id 𝓛 (𝓝 g)
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds id g]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨A, hA, hAA⟩ := hunif k n (ε / 2) (half_pos hε)
  filter_upwards [hA] with f hf
  show SchwartzMap.seminorm ℝ k n (f - g) < ε
  refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun x => ?_) (half_lt_self hε)
  rw [sch_sub_iter]
  have : iteratedFDeriv ℝ n (g : E → F) x = D n x := by
    show iteratedFDeriv ℝ n G x = D n x
    rw [hit n]
  rw [this]
  exact hAA f hf x

end complete

/-! ### summability in complete locally convex spaces -/

section summ

lemma summable_of_sn {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [CompleteSpace E] {κ : Type*} {p : SeminormFamily ℂ E κ} (hp : WithSeminorms p) {ι : Type*}
    (a : ι → E) (h : ∀ i, Summable fun j => p i (a j)) : Summable a := by
  classical
  rw [summable_iff_vanishing]
  intro e he
  obtain ⟨s, r, hr, hsr⟩ := (hp.mem_nhds_iff 0 e).1 he
  have hq : Summable fun j => ∑ i ∈ s, p i (a j) := summable_sum fun i _ => h i
  obtain ⟨S, hS⟩ := (summable_iff_vanishing.1 hq) (Metric.ball 0 r) (Metric.ball_mem_nhds 0 hr)
  refine ⟨S, fun t ht => hsr ?_⟩
  have h1 := hS t ht
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at h1
  rw [Seminorm.mem_ball_zero]
  calc (s.sup p) (∑ j ∈ t, a j) ≤ ∑ j ∈ t, (s.sup p) (a j) :=
        Finset.le_sum_of_subadditive (⇑(s.sup p)) (map_zero _).le (map_add_le_add _) t a
    _ ≤ ∑ j ∈ t, ∑ i ∈ s, p i (a j) := Finset.sum_le_sum fun j _ =>
        Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun i _ => apply_nonneg _ _) fun i hi =>
          Finset.single_le_sum (f := fun i => p i (a j)) (fun i _ => apply_nonneg _ _) hi
    _ ≤ |∑ j ∈ t, ∑ i ∈ s, p i (a j)| := le_abs_self _
    _ < r := h1

end summ

/-! ### summability in complete locally convex spaces, and the reconstruction formula -/


section recon

lemma wsum : Summable fun n : Fin m → ℤ => ((1 + ‖wlat n‖) ^ (2 * m))⁻¹ :=
  Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => weight_le (wlat n) n fun i => by
      rw [wlat_apply]; linarith [abs_nonneg (n i : ℝ)])
    (prod_summable gw_nonneg gw_summable)

def evx (x : V m) : StrongDual ℂ (Sch m) :=
  (BoundedContinuousFunction.evalCLM ℂ x) ∘L (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (V m) ℂ)

lemma evx_apply (x : V m) (f : Sch m) : evx x f = f x := rfl

lemma fiber_hasSum (f : Sch m) (x : V m) (n : Fin m → ℤ) :
    HasSum (fun ξ : Fin m → ℤ => phiF n ξ f * eF n ξ x) ((chi (x - vlat n) : ℂ) * f x) := by
  by_cases hθ : tht (x - vlat n) = 0
  · have hc : chi (x - vlat n) = 0 := by
      by_contra h; rw [tht_chi h] at hθ; exact one_ne_zero hθ
    have : (fun ξ : Fin m → ℤ => phiF n ξ f * eF n ξ x) = fun _ => 0 := by
      funext ξ; rw [eF_apply, thtC, hθ]; simp
    rw [this, hc]
    simpa using hasSum_zero
  · have hy : ∀ i, |(x - vlat n) i| < 1 / 2 := by
      intro i
      by_contra h'
      exact hθ (tht_zero i (by linarith [not_lt.1 h']))
    let h : V m → ℂ := fun y => chiC y * f (y + vlat n)
    have hc : Continuous h :=
      (Complex.continuous_ofReal.comp chi_smooth.continuous).mul
        (f.continuous.comp (continuous_id.add continuous_const))
    have hsupp : ∀ y, h y ≠ 0 → ∀ i, |y i| < 3 / 8 := by
      intro y hy i
      have : chi y ≠ 0 := by
        intro h0; apply hy; simp [h, chiC, h0]
      exact chi_supp this i
    obtain ⟨q, -, hqb⟩ := phiF_decay (m := m) (2 * m)
    have hsum : Summable fun ξ : Fin m → ℤ => 𝓕 h (wlat ξ) := by
      refine Summable.of_norm_bounded (g := fun ξ => q f * ((1 + ‖wlat ξ‖) ^ (2 * m))⁻¹)
        (wsum.mul_left _) fun ξ => ?_
      have e : 𝓕 h (wlat ξ) = phiF n ξ f := (phiF_apply n ξ f).symm
      rw [e]
      have h1 := hqb n ξ f
      have hw : 0 < (1 + ‖wlat ξ‖) ^ (2 * m) := by positivity
      have hv : 1 ≤ (1 + ‖vlat n‖) ^ (2 * m) := one_le_pow₀ (by linarith [norm_nonneg (vlat n)])
      rw [mul_comm, ← div_eq_inv_mul, le_div_iff₀ hw]
      calc ‖phiF n ξ f‖ * (1 + ‖wlat ξ‖) ^ (2 * m)
          ≤ (1 + ‖wlat ξ‖) ^ (2 * m) * (1 + ‖vlat n‖) ^ (2 * m) * ‖phiF n ξ f‖ := by
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact le_mul_of_one_le_right hw.le hv
        _ ≤ q f := h1
    have hfs := (fs_hasSum h hc hsupp hsum (x - vlat n) hy).mul_left (thtC (x - vlat n))
    have e1 : thtC (x - vlat n) * h (x - vlat n) = (chi (x - vlat n) : ℂ) * f x := by
      simp only [h, chiC, thtC, sub_add_cancel]
      by_cases hc0 : chi (x - vlat n) = 0
      · simp [hc0]
      · rw [tht_chi hc0]; push_cast; ring
    rw [e1] at hfs
    have e2 : (fun ξ : Fin m → ℤ => phiF n ξ f * eF n ξ x) =
        fun ξ => thtC (x - vlat n) * (𝓕 h (wlat ξ) * ech (inner ℝ (x - vlat n) (wlat ξ))) := by
      funext ξ
      rw [phiF_apply, eF_apply]
      ring
    rw [e2]
    exact hfs

theorem frame_hasSum (f : Sch m) :
    HasSum (fun j : (Fin m → ℤ) × (Fin m → ℤ) => phiF j.1 j.2 f • eF j.1 j.2) f := by
  have hsm : Summable (fun j : (Fin m → ℤ) × (Fin m → ℤ) => phiF j.1 j.2 f • eF j.1 j.2) := by
    refine summable_of_sn (schwartz_withSeminorms ℂ (V m) ℂ) _ fun i => ?_
    obtain ⟨P', -, hP'⟩ := frame_dom (schwartzSeminormFamily ℂ (V m) ℂ i)
      ((schwartz_withSeminorms ℂ (V m) ℂ).continuous_seminorm i)
    refine Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) (fun j => ?_)
      (cw_summable.mul_right (P' f))
    rw [map_smul_eq_mul, mul_comm]
    exact hP' j f
  obtain ⟨g, hg⟩ := hsm
  have hgf : g = f := by
    ext x
    have h1 : HasSum (fun j : (Fin m → ℤ) × (Fin m → ℤ) => phiF j.1 j.2 f * eF j.1 j.2 x) (g x) := by
      have := (evx x).hasSum hg
      simpa [evx_apply, map_smul, smul_eq_mul] using this
    have h2 := h1.prod_fiberwise fun n => fiber_hasSum f x n
    have h3 : HasSum (fun n : Fin m → ℤ => (chi (x - vlat n) : ℂ) * f x) (f x) := by
      have := (Complex.ofRealCLM.hasSum (chi_hasSum x)).mul_right (f x)
      simpa using this
    exact h2.unique h3
  rw [hgf] at hg
  exact hg

end recon

/-! ### general locally convex helpers -/

section helpers

open MasulloGRH TensorProduct Bornology

lemma sn_scale {V : Type*} [AddCommGroup V] [Module ℂ V] {σ β : Seminorm ℂ V} {r M : ℝ} (hr : 0 < r)
    (hM : 0 ≤ M) (h : ∀ y, β y < r → σ y ≤ M) (y : V) : σ y ≤ M / r * β y := by
  by_contra hcon
  push Not at hcon
  have hβ := apply_nonneg β y
  have hσpos : 0 < σ y := lt_of_le_of_lt (by positivity) hcon
  have key : M * β y < r * σ y := by
    have := hcon
    rw [div_mul_eq_mul_div, div_lt_iff₀ hr] at this
    linarith
  obtain ⟨t, ht0, ht1, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t * β y < r ∧ M < t * σ y := by
    by_cases hβ0 : β y = 0
    · refine ⟨(M + 1) / σ y, by positivity, ?_, ?_⟩
      · rw [hβ0, mul_zero]; exact hr
      · rw [div_mul_cancel₀ _ hσpos.ne']; linarith
    · have hβp : 0 < β y := lt_of_le_of_ne hβ (Ne.symm hβ0)
      refine ⟨(M / σ y + r / β y) / 2, by positivity, ?_, ?_⟩
      · have h1 : M / σ y < r / β y := by
          rw [div_lt_div_iff₀ hσpos hβp]; linarith
        have : (M / σ y + r / β y) / 2 < r / β y := by linarith
        calc (M / σ y + r / β y) / 2 * β y < r / β y * β y :=
              mul_lt_mul_of_pos_right this hβp
          _ = r := div_mul_cancel₀ _ hβp.ne'
      · have h1 : M / σ y < r / β y := by
          rw [div_lt_div_iff₀ hσpos hβp]; linarith
        have : M / σ y < (M / σ y + r / β y) / 2 := by linarith
        calc M = M / σ y * σ y := (div_mul_cancel₀ _ hσpos.ne').symm
          _ < (M / σ y + r / β y) / 2 * σ y := mul_lt_mul_of_pos_right this hσpos
  have e1 : β ((t : ℂ) • y) = t * β y := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have e2 : σ ((t : ℂ) • y) = t * σ y := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have := h ((t : ℂ) • y) (by rw [e1]; exact ht1)
  rw [e2] at this
  linarith

lemma bdd_of_cont {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {q : Seminorm ℂ E} (hq : Continuous q) {S : Set E}
    (hS : IsVonNBounded ℂ S) : ∃ R : ℝ, ∀ x ∈ S, q x ≤ R := by
  obtain ⟨a, ha⟩ := (hS (q.ball_mem_nhds hq one_pos)).eventually.exists
  refine ⟨‖a‖, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := ha hx
  rw [map_smul_eq_mul]
  have h1 : q y < 1 := (Seminorm.mem_ball_zero q).1 hy
  exact mul_le_of_le_one_right (norm_nonneg a) h1.le

lemma lc_of_ws {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {ι : Type u}
    {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    IsLocallyConvexTopology E ‹TopologicalSpace E› :=
  ⟨Finset ι, inferInstance, fun s => s.sup p, hp.finset_sups⟩

lemma eqc_bound {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] {κ : Type*}
    {q : SeminormFamily ℂ V κ} (hq : WithSeminorms q) {A : Set (StrongDual ℂ V)}
    (hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ V) : V → ℂ))) :
    ∃ σ : Seminorm ℂ V, Continuous σ ∧ ∀ a ∈ A, ∀ x, ‖a x‖ ≤ σ x := by
  have h0 := hA 0
  rw [Metric.equicontinuousAt_iff_right] at h0
  obtain ⟨s, r, hr, hsr⟩ := (hq.mem_nhds_iff 0 _).1 (h0 1 one_pos)
  refine ⟨(1 / r).toNNReal • s.sup q, ?_, ?_⟩
  · have h := (hq.finset_sups.continuous_seminorm s).const_smul ((1 / r).toNNReal)
    rw [FunLike.coe_smul]
    exact h
  · intro a ha x
    have key : ∀ y, (s.sup q) y < r → ((normSeminorm ℂ ℂ).comp (a : V →ₗ[ℂ] ℂ)) y ≤ 1 := by
      intro y hy
      have hy' : y ∈ (s.sup q).ball 0 r := by rw [Seminorm.mem_ball_zero]; exact hy
      have h := hsr hy' ⟨a, ha⟩
      simp only [map_zero, dist_zero_left] at h
      exact h.le
    have h := sn_scale hr zero_le_one key x
    have e : ((1 / r).toNNReal • s.sup q) x = 1 / r * (s.sup q) x := by
      rw [smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by positivity)]
    rw [e]
    exact h

lemma eqc_of_bound {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (A : Set (StrongDual ℂ V)) (σ : Seminorm ℂ V) (hσ : Continuous σ)
    (h : ∀ a ∈ A, ∀ x, ‖a x‖ ≤ σ x) :
    Equicontinuous (fun a : A => ((a : StrongDual ℂ V) : V → ℂ)) := by
  apply equicontinuous_of_equicontinuousAt_zero (fun a : A => (a : StrongDual ℂ V))
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hev : ∀ᶠ x in 𝓝 (0 : V), σ x < ε := by
    have := hσ.tendsto 0
    rw [map_zero] at this
    exact this.eventually (Iio_mem_nhds hε)
  filter_upwards [hev] with x hx a
  simp only [Function.comp_apply, map_zero, dist_zero_left]
  exact lt_of_le_of_lt (h a a.2 x) hx

lemma hb_norm {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] {κ : Type*}
    {q : SeminormFamily ℂ V κ} (hq : WithSeminorms q) (β : Seminorm ℂ V) (hβ : Continuous β)
    (y : V) : ∃ g : StrongDual ℂ V, (∀ z, ‖g z‖ ≤ β z) ∧ ‖g y‖ = β y := by
  have : PolynormableSpace ℂ V := hq.toPolynormableSpace
  by_cases hy : y = 0
  · exact ⟨0, fun z => by simp, by simp [hy]⟩
  · let T := LinearEquiv.toSpanNonzeroSingleton ℂ V y hy
    let f : Module.Dual ℂ (ℂ ∙ y) := (β y : ℂ) • (T.symm : (ℂ ∙ y) →ₗ[ℂ] ℂ)
    have hf : ∀ z : (ℂ ∙ y), ‖f z‖ ≤ β z := by
      intro z
      have hz : T.symm z • y = (z : V) := LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul ℂ V y hy z
      rw [← hz, map_smul_eq_mul]
      simp only [f, LinearMap.smul_apply, LinearEquiv.coe_coe, smul_eq_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg β y)]
      rw [mul_comm]
    obtain ⟨g, hg, hgle⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm (ℂ ∙ y) f hβ hf
    refine ⟨g, hgle, ?_⟩
    have h1 := hg ⟨y, Submodule.mem_span_singleton_self y⟩
    have h2 : T.symm ⟨y, Submodule.mem_span_singleton_self y⟩ = 1 := by
      rw [LinearEquiv.symm_apply_eq]
      ext
      simp [T]
    have h3 : g y = (β y : ℂ) := by
      rw [h1]
      simp only [f, LinearMap.smul_apply, LinearEquiv.coe_coe, h2, smul_eq_mul, mul_one]
    rw [h3, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg β y)]

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [τV : TopologicalSpace V]
variable {F : Type u} [AddCommGroup F] [Module ℂ F]

def kapA (a : V →ₗ[ℂ] ℂ) : V ⊗[ℂ] F →ₗ[ℂ] F :=
  (TensorProduct.lid ℂ F).toLinearMap ∘ₗ TensorProduct.map a LinearMap.id

omit τV in
@[simp] lemma kapA_tmul (a : V →ₗ[ℂ] ℂ) (x : V) (y : F) :
    kapA (F := F) a (x ⊗ₜ y) = a x • y := by
  simp [kapA]

variable [τF : TopologicalSpace F]

lemma tf_sub (ab : StrongDual ℂ V × StrongDual ℂ F) (u v : V ⊗[ℂ] F) :
    tensorFunctional V F ab (u - v) = tensorFunctional V F ab u - tensorFunctional V F ab v := by
  simp [tensorFunctional, map_sub]

lemma tf_kapA (a : StrongDual ℂ V) (g : StrongDual ℂ F) (w : V ⊗[ℂ] F) :
    tensorFunctional V F (a, g) w = g (kapA (a : V →ₗ[ℂ] ℂ) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [tensorFunctional]
  | tmul x y => simp [tensorFunctional, kapA_tmul]
  | add u v hu hv =>
    rw [map_add, map_add, ← hu, ← hv]
    simp [tensorFunctional, map_add]

lemma tf_tmul (ab : StrongDual ℂ V × StrongDual ℂ F) (x : V) (y : F) :
    tensorFunctional V F ab (x ⊗ₜ y) = ab.1 x * ab.2 y := by
  simp [tensorFunctional]

lemma tf_add (ab : StrongDual ℂ V × StrongDual ℂ F) (u v : V ⊗[ℂ] F) :
    tensorFunctional V F ab (u + v) = tensorFunctional V F ab u + tensorFunctional V F ab v := by
  simp [tensorFunctional, map_add]

lemma bilb {κV : Type*} {qV : SeminormFamily ℂ V κV} (hqV : WithSeminorms qV)
    {κ : Type*} {q : SeminormFamily ℂ F κ} (hq : WithSeminorms q)
    [t : TopologicalSpace (V ⊗[ℂ] F)] {ι' : Type*}
    {p : SeminormFamily ℂ (V ⊗[ℂ] F) ι'} (hp : WithSeminorms p)
    (hc : Continuous (fun p : V × F => p.1 ⊗ₜ[ℂ] p.2)) (k : ι') :
    ∃ s : Finset κV, ∃ β0 : Seminorm ℂ F, Continuous β0 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ x y, p k (x ⊗ₜ y) ≤ c * (s.sup qV) x * β0 y := by
  have h0 : (fun p : V × F => p.1 ⊗ₜ[ℂ] p.2) ⁻¹' {u | p k u < 1} ∈ 𝓝 ((0 : V), (0 : F)) := by
    apply hc.continuousAt.preimage_mem_nhds
    show (p k) ⁻¹' Set.Iio 1 ∈ 𝓝 ((0 : V) ⊗ₜ[ℂ] (0 : F))
    rw [zero_tmul]
    exact (hp.continuous_seminorm k).continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact Iio_mem_nhds one_pos)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at h0
  obtain ⟨U, hU, W, hW, hUW⟩ := h0
  obtain ⟨s, r, hr, hsU⟩ := (hqV.mem_nhds_iff 0 U).1 hU
  obtain ⟨s', r', hr', hsW⟩ := (hq.mem_nhds_iff 0 W).1 hW
  let α0 : Seminorm ℂ V := s.sup qV
  let β0 : Seminorm ℂ F := s'.sup q
  have key : ∀ x y, α0 x < r → β0 y < r' → p k (x ⊗ₜ y) < 1 := by
    intro x y hx hy
    have hxU : x ∈ U := hsU (by rw [Seminorm.mem_ball_zero]; exact hx)
    have hyW : y ∈ W := hsW (by rw [Seminorm.mem_ball_zero]; exact hy)
    exact hUW (Set.mk_mem_prod hxU hyW)
  have step1 : ∀ y, β0 y < r' → ∀ x, p k (x ⊗ₜ y) ≤ 1 / r * α0 x := by
    intro y hy x
    exact sn_scale (σ := (p k).comp ((TensorProduct.mk ℂ V F).flip y)) (β := α0) hr zero_le_one
      (fun x hx => by
        show p k (x ⊗ₜ y) ≤ 1
        exact (key x y hx hy).le) x
  refine ⟨s, β0, hq.finset_sups.continuous_seminorm s', 1 / (r * r'), by positivity,
    fun x y => ?_⟩
  have := sn_scale (σ := (p k).comp (TensorProduct.mk ℂ V F x)) (β := β0) hr'
    (M := 1 / r * α0 x) (by positivity) (fun y hy => step1 y hy x) y
  have e : 1 / r * α0 x / r' * β0 y = 1 / (r * r') * α0 x * β0 y := by
    field_simp
  rw [← e]
  exact this

end helpers

/-! ### nuclearity from a nuclear frame -/

section nucgen

open MasulloGRH TensorProduct Bornology

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {F : Type u} [AddCommGroup F] [Module ℂ F] [τF : TopologicalSpace F]

/-- index type of the `ε`-seminorms -/
abbrev EI (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] : Type u :=
  {A : Set (StrongDual ℂ E) // Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ))} ×
  {B : Set (StrongDual ℂ F) // Equicontinuous (fun b : B => ((b : StrongDual ℂ F) : F → ℂ))}

def tfL (ab : StrongDual ℂ E × StrongDual ℂ F) : E ⊗[ℂ] F →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ TensorProduct.map (ab.1 : E →ₗ[ℂ] ℂ) (ab.2 : F →ₗ[ℂ] ℂ)

lemma tfL_apply (ab : StrongDual ℂ E × StrongDual ℂ F) (u : E ⊗[ℂ] F) :
    tfL ab u = tensorFunctional E F ab u := rfl

/-- the `ε`-seminorm attached to equicontinuous sets `A`, `B` -/
def esn (AB : EI E F) : Seminorm ℂ (E ⊗[ℂ] F) :=
  ⨆ ab : AB.1.1 ×ˢ AB.2.1, (normSeminorm ℂ ℂ).comp (tfL (ab : StrongDual ℂ E × StrongDual ℂ F))

variable {κE : Type*} {pE : SeminormFamily ℂ E κE} (hE : WithSeminorms pE)
variable {κ : Type*} {q : SeminormFamily ℂ F κ} (hq : WithSeminorms q)

include hE hq

lemma esn_bdd (AB : EI E F) : ∃ σ : Seminorm ℂ E, Continuous σ ∧ ∃ β : Seminorm ℂ F, Continuous β ∧
    ∀ ab ∈ AB.1.1 ×ˢ AB.2.1, ∀ x y, ‖ab.1 x‖ ≤ σ x ∧ ‖ab.2 y‖ ≤ β y := by
  obtain ⟨σ, hσ, hσA⟩ := eqc_bound hE AB.1.2
  obtain ⟨β, hβ, hβB⟩ := eqc_bound hq AB.2.2
  exact ⟨σ, hσ, β, hβ, fun ab hab x y => ⟨hσA _ hab.1 x, hβB _ hab.2 y⟩⟩

lemma esn_range_bdd (AB : EI E F) :
    BddAbove (Set.range fun ab : AB.1.1 ×ˢ AB.2.1 =>
      (normSeminorm ℂ ℂ).comp (tfL (ab : StrongDual ℂ E × StrongDual ℂ F))) := by
  rw [Seminorm.bddAbove_range_iff]
  intro u
  obtain ⟨σ, -, β, -, hb⟩ := esn_bdd hE hq AB
  have : ∃ M, ∀ ab ∈ AB.1.1 ×ˢ AB.2.1, ‖tensorFunctional E F ab u‖ ≤ M := by
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, fun ab _ => by simp [tensorFunctional]⟩
    | tmul x y =>
      refine ⟨σ x * β y, fun ab hab => ?_⟩
      rw [tf_tmul, norm_mul]
      exact mul_le_mul (hb ab hab x y).1 (hb ab hab x y).2 (norm_nonneg _) (apply_nonneg _ _)
    | add u v hu hv =>
      obtain ⟨M1, h1⟩ := hu
      obtain ⟨M2, h2⟩ := hv
      refine ⟨M1 + M2, fun ab hab => ?_⟩
      rw [tf_add]
      exact (norm_add_le _ _).trans (add_le_add (h1 ab hab) (h2 ab hab))
  obtain ⟨M, hM⟩ := this
  refine ⟨M, ?_⟩
  rintro _ ⟨ab, rfl⟩
  exact hM ab ab.2

lemma esn_apply (AB : EI E F) (u : E ⊗[ℂ] F) :
    esn AB u = ⨆ ab : AB.1.1 ×ˢ AB.2.1, ‖tensorFunctional E F ab u‖ := by
  rw [esn, Seminorm.iSup_apply (esn_range_bdd hE hq AB)]
  rfl

lemma le_esn (AB : EI E F) (u : E ⊗[ℂ] F) (ab : StrongDual ℂ E × StrongDual ℂ F)
    (hab : ab ∈ AB.1.1 ×ˢ AB.2.1) : ‖tensorFunctional E F ab u‖ ≤ esn AB u := by
  have h := esn_range_bdd hE hq AB
  rw [Seminorm.bddAbove_range_iff] at h
  rw [esn_apply hE hq]
  exact le_ciSup (h u) (⟨ab, hab⟩ : AB.1.1 ×ˢ AB.2.1)

lemma esn_le (AB : EI E F) (u : E ⊗[ℂ] F) {M : ℝ} (hM0 : 0 ≤ M)
    (h : ∀ ab ∈ AB.1.1 ×ˢ AB.2.1, ‖tensorFunctional E F ab u‖ ≤ M) : esn AB u ≤ M := by
  rw [esn_apply hE hq]
  exact Real.iSup_le (fun ab => h ab ab.2) hM0

def efam : SeminormFamily ℂ (E ⊗[ℂ] F) (EI E F) := fun AB => esn AB

lemma eps_tmul_cont [t : TopologicalSpace (E ⊗[ℂ] F)] (ht : WithSeminorms (efam (E := E) (F := F))) :
    Continuous (fun p : E × F => p.1 ⊗ₜ[ℂ] p.2) := by
  have := hE.topologicalAddGroup
  have := hq.topologicalAddGroup
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, y0⟩
  rw [ContinuousAt, ht.tendsto_nhds]
  intro AB ε hε
  obtain ⟨σ, hσ, β, hβ, hb⟩ := esn_bdd hE hq AB
  have htm : ∀ x y, esn AB (x ⊗ₜ y) ≤ σ x * β y := fun x y =>
    esn_le hE hq AB _ (by positivity) fun ab hab => by
      rw [tf_tmul, norm_mul]
      exact mul_le_mul (hb ab hab x y).1 (hb ab hab x y).2 (norm_nonneg _) (apply_nonneg _ _)
  let g : E × F → ℝ := fun p => σ (p.1 - x0) * β (p.2 - y0) + σ x0 * β (p.2 - y0) +
    σ (p.1 - x0) * β y0
  have hg : Continuous g := by
    have h1 : Continuous fun p : E × F => σ (p.1 - x0) := hσ.comp (continuous_fst.sub continuous_const)
    have h2 : Continuous fun p : E × F => β (p.2 - y0) := hβ.comp (continuous_snd.sub continuous_const)
    exact ((h1.mul h2).add (continuous_const.mul h2)).add (h1.mul continuous_const)
  have hg0 : g (x0, y0) = 0 := by simp [g]
  have hev := (hg.tendsto (x0, y0)).eventually (Iio_mem_nhds (show g (x0, y0) < ε by rw [hg0]; exact hε))
  filter_upwards [hev] with p hp
  show esn AB (p.1 ⊗ₜ p.2 - x0 ⊗ₜ y0) < ε
  have e : p.1 ⊗ₜ[ℂ] p.2 - x0 ⊗ₜ y0 =
      (p.1 - x0) ⊗ₜ (p.2 - y0) + x0 ⊗ₜ (p.2 - y0) + (p.1 - x0) ⊗ₜ y0 := by
    simp only [sub_tmul, tmul_sub]; abel
  rw [e]
  have h1 := map_add_le_add (esn AB) ((p.1 - x0) ⊗ₜ[ℂ] (p.2 - y0) + x0 ⊗ₜ (p.2 - y0))
    ((p.1 - x0) ⊗ₜ y0)
  have h2 := map_add_le_add (esn AB) ((p.1 - x0) ⊗ₜ[ℂ] (p.2 - y0)) (x0 ⊗ₜ (p.2 - y0))
  have h3 := htm (p.1 - x0) (p.2 - y0)
  have h4 := htm x0 (p.2 - y0)
  have h5 := htm (p.1 - x0) y0
  have hp' : g p < ε := hp
  simp only [g] at hp'
  linarith

lemma tE_le_eps [t : TopologicalSpace (E ⊗[ℂ] F)] (ht : WithSeminorms (efam (E := E) (F := F))) :
    t ≤ epsTensorTopology E F := by
  have := ht.topologicalAddGroup
  rw [epsTensorTopology, ← continuous_iff_le_induced, continuous_iff_continuousAt]
  intro u0
  rw [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  rintro S ⟨A, B, hA, hB, rfl⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let AB : EI E F := (⟨A, hA⟩, ⟨B, hB⟩)
  have hN := ht.continuous_seminorm AB
  have hev : ∀ᶠ u in 𝓝 u0, esn AB (u - u0) < ε := by
    have h : Tendsto (fun u => esn AB (u - u0)) (𝓝 u0) (𝓝 (esn AB (u0 - u0))) :=
      (hN.comp (continuous_sub_right u0)).tendsto u0
    rw [sub_self, map_zero] at h
    exact h.eventually (Iio_mem_nhds hε)
  filter_upwards [hev] with u hu
  intro ab hab
  change dist (tensorFunctional E F ab u0) (tensorFunctional E F ab u) < ε
  rw [dist_eq_norm, norm_sub_rev, ← tf_sub]
  exact lt_of_le_of_lt (le_esn hE hq AB _ ab hab) hu

lemma proj_le_eps : projTensorTopology E F ≤ epsTensorTopology E F := by
  let tE : TopologicalSpace (E ⊗[ℂ] F) := (efam (E := E) (F := F)).moduleFilterBasis.topology
  have htE : @WithSeminorms ℂ (E ⊗[ℂ] F) (EI E F) _ _ _ (efam (E := E) (F := F)) tE := ⟨rfl⟩
  calc projTensorTopology E F ≤ tE :=
        sInf_le ⟨lc_of_ws htE, eps_tmul_cont hE hq (t := tE) htE⟩
    _ ≤ epsTensorTopology E F := tE_le_eps hE hq (t := tE) htE

end nucgen

section nucframe

open MasulloGRH TensorProduct Bornology

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {F : Type u} [AddCommGroup F] [Module ℂ F] [τF : TopologicalSpace F]
variable {κE : Type*} {pE : SeminormFamily ℂ E κE} (hE : WithSeminorms pE)
variable {κ : Type*} {q : SeminormFamily ℂ F κ} (hq : WithSeminorms q)
variable {ι : Type*} (φ : ι → StrongDual ℂ E) (e : ι → E) (c : ι → ℝ)
variable (hexp : ∀ x, HasSum (fun j => φ j x • e j) x)
variable (hc0 : ∀ j, 0 < c j) (hcs : Summable c)
variable (hdom : ∀ P : Seminorm ℂ E, Continuous P → ∃ P' : Seminorm ℂ E, Continuous P' ∧
  ∀ j x, P (e j) * ‖φ j x‖ ≤ c j * P' x)

omit τF in
lemma kapA_sum (a : E →ₗ[ℂ] ℂ) (S : Finset (E × F)) :
    kapA (F := F) a (∑ z ∈ S, z.1 ⊗ₜ z.2) = ∑ z ∈ S, a z.1 • z.2 := by
  simp [map_sum]

include hE hexp in
/-- the key estimate: `p (w) ≤ c₀ ∑ α₀(e_j) β₀(κ_j w)` -/
lemma key_est {α0 : Seminorm ℂ E} (hα0 : Continuous α0) (β0 : Seminorm ℂ F) {c0 : ℝ}
    (P : Seminorm ℂ (E ⊗[ℂ] F)) (hP : ∀ x y, P (x ⊗ₜ y) ≤ c0 * α0 x * β0 y) (hc00 : 0 < c0)
    (hsum : ∀ w : E ⊗[ℂ] F, Summable fun j => α0 (e j) * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) w))
    (w : E ⊗[ℂ] F) :
    P w ≤ c0 * ∑' j, α0 (e j) * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) w) := by
  classical
  have := hE.topologicalAddGroup
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset w
  -- remainder after projecting on the finitely many frame vectors in `J`
  let R : Finset ι → ℝ := fun J => ∑ z ∈ S, c0 * α0 (z.1 - ∑ j ∈ J, φ j z.1 • e j) * β0 z.2
  have hR : Tendsto R atTop (𝓝 0) := by
    have : Tendsto R atTop (𝓝 (∑ z ∈ S, c0 * α0 (z.1 - z.1) * β0 z.2)) := by
      refine tendsto_finsetSum _ fun z _ => ?_
      refine ((tendsto_const_nhds.mul ?_).mul tendsto_const_nhds)
      exact (hα0.tendsto _).comp (tendsto_const_nhds.sub (hexp z.1))
    simpa using this
  have hbound : ∀ J : Finset ι, P w ≤ R J + c0 * ∑' j, α0 (e j) * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) w) := by
    intro J
    have hw : w = ∑ z ∈ S, (z.1 - ∑ j ∈ J, φ j z.1 • e j) ⊗ₜ z.2 +
        ∑ j ∈ J, e j ⊗ₜ kapA (φ j : E →ₗ[ℂ] ℂ) w := by
      conv_lhs => rw [hS]
      rw [hS]
      simp only [kapA_sum, ContinuousLinearMap.coe_coe, tmul_sum, sub_tmul, Finset.sum_sub_distrib,
        sum_tmul, tmul_smul, smul_tmul']
      rw [Finset.sum_comm]
      abel
    calc P w ≤ P (∑ z ∈ S, (z.1 - ∑ j ∈ J, φ j z.1 • e j) ⊗ₜ z.2) +
          P (∑ j ∈ J, e j ⊗ₜ kapA (φ j : E →ₗ[ℂ] ℂ) w) := by
          conv_lhs => rw [hw]
          exact map_add_le_add _ _ _
      _ ≤ R J + c0 * ∑ j ∈ J, α0 (e j) * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) w) := by
          refine add_le_add ?_ ?_
          · refine (Finset.le_sum_of_subadditive (⇑P) (map_zero _).le (map_add_le_add _) _ _).trans ?_
            exact Finset.sum_le_sum fun z _ => hP _ _
          · refine (Finset.le_sum_of_subadditive (⇑P) (map_zero _).le (map_add_le_add _) _ _).trans ?_
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun j _ => by rw [← mul_assoc]; exact hP _ _
      _ ≤ R J + c0 * ∑' j, α0 (e j) * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) w) := by
          gcongr
          exact (hsum w).sum_le_tsum _ fun j _ => mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have := ge_of_tendsto (hR.add_const (c0 * ∑' j, α0 (e j) * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) w)))
    (Eventually.of_forall hbound)
  simpa using this

include hE hq hexp hc0 hcs hdom in
lemma eps_le_piF (t' : TopologicalSpace (E ⊗[ℂ] F))
    (ht' : t' ∈ {t | IsLocallyConvexTopology (E ⊗[ℂ] F) t ∧
      @Continuous (E × F) (E ⊗[ℂ] F) _ t (fun p => p.1 ⊗ₜ[ℂ] p.2)}) :
    epsTensorTopology E F ≤ t' := by
  classical
  obtain ⟨⟨ι', _, p, hp⟩, hc⟩ := ht'
  have := hE.topologicalAddGroup
  have := hq.topologicalAddGroup
  refine (@continuous_id_iff_le _ (epsTensorTopology E F) t').1 ?_
  rw [@continuous_iff_continuousAt _ _ (epsTensorTopology E F) t']
  intro u0
  show Tendsto id (@nhds _ (epsTensorTopology E F) u0) (𝓝 u0)
  rw [hp.tendsto_nhds id u0]
  intro k ε hε
  obtain ⟨s, β0, hβ0, c0, hc00, hbil⟩ := bilb hE hq hp hc k
  let α0 : Seminorm ℂ E := s.sup pE
  have hα0 : Continuous α0 := hE.finset_sups.continuous_seminorm s
  obtain ⟨α', hα', hdα⟩ := hdom α0 hα0
  -- summability of the key series
  have hsum : ∀ w : E ⊗[ℂ] F, Summable fun j => α0 (e j) * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) w) := by
    intro w
    obtain ⟨S, hS⟩ := TensorProduct.exists_finset w
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (fun j => ?_) (hcs.mul_right (∑ z ∈ S, α' z.1 * β0 z.2))
    rw [hS, kapA_sum]
    calc α0 (e j) * β0 (∑ z ∈ S, (φ j : E →ₗ[ℂ] ℂ) z.1 • z.2)
        ≤ α0 (e j) * ∑ z ∈ S, ‖φ j z.1‖ * β0 z.2 := by
          refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _)
          refine (Finset.le_sum_of_subadditive (⇑β0) (map_zero _).le (map_add_le_add _) _ _).trans ?_
          exact Finset.sum_le_sum fun z _ => by rw [map_smul_eq_mul]; rfl
      _ = ∑ z ∈ S, (α0 (e j) * ‖φ j z.1‖) * β0 z.2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ ∑ z ∈ S, (c j * α' z.1) * β0 z.2 :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hdα j z.1) (apply_nonneg _ _)
      _ = c j * ∑ z ∈ S, α' z.1 * β0 z.2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring
  -- the equicontinuous sets
  let a : ι → StrongDual ℂ E := fun j => ((α0 (e j) / c j : ℝ) : ℂ) • φ j
  let A : Set (StrongDual ℂ E) := Set.range a
  let B : Set (StrongDual ℂ F) := {g | ∀ y, ‖g y‖ ≤ β0 y}
  have hA : Equicontinuous (fun a : A => ((a : StrongDual ℂ E) : E → ℂ)) := by
    refine eqc_of_bound A α' hα' ?_
    rintro _ ⟨j, rfl⟩ x
    simp only [a, ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (div_nonneg (apply_nonneg _ _) (hc0 j).le), div_mul_eq_mul_div,
      div_le_iff₀ (hc0 j), mul_comm (α' x)]
    exact hdα j x
  have hB : Equicontinuous (fun g : B => ((g : StrongDual ℂ F) : F → ℂ)) :=
    eqc_of_bound B β0 hβ0 (fun g hg => hg)
  let 𝔖 : Set (Set (StrongDual ℂ E × StrongDual ℂ F)) :=
    {S | ∃ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)),
      Equicontinuous (fun a : A => (a : E → ℂ)) ∧
      Equicontinuous (fun b : B => (b : F → ℂ)) ∧ S = A ×ˢ B}
  have hS : A ×ˢ B ∈ 𝔖 := ⟨A, B, hA, hB, rfl⟩
  let Φ : E ⊗[ℂ] F → _ := fun u => UniformOnFun.ofFun 𝔖 (fun ab => tensorFunctional E F ab u)
  have hT : Tendsto Φ (@nhds _ (epsTensorTopology E F) u0) (𝓝 (Φ u0)) := by
    show Tendsto Φ (@nhds _ (TopologicalSpace.induced Φ inferInstance) u0) (𝓝 (Φ u0))
    rw [nhds_induced]
    exact tendsto_comap
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at hT
  let δ : ℝ := ε / (c0 * ∑' j, c j + 1)
  have hcsum0 : 0 ≤ ∑' j, c j := tsum_nonneg fun j => (hc0 j).le
  have hδ : 0 < δ := by positivity
  have hev := Metric.tendstoUniformlyOn_iff.1 (hT _ hS) δ hδ
  filter_upwards [hev] with u hu
  show p k (u - u0) < ε
  have hj : ∀ j, α0 (e j) * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) (u - u0)) ≤ c j * δ := by
    intro j
    obtain ⟨g, hgB, hgy⟩ := hb_norm hq β0 hβ0 (kapA (φ j : E →ₗ[ℂ] ℂ) (u - u0))
    have h1 := hu (a j, g) ⟨⟨j, rfl⟩, hgB⟩
    change dist (tensorFunctional E F (a j, g) u0) (tensorFunctional E F (a j, g) u) < δ at h1
    rw [dist_eq_norm, norm_sub_rev, ← tf_sub, tf_kapA] at h1
    have e1 : kapA (a j : E →ₗ[ℂ] ℂ) (u - u0) =
        ((α0 (e j) / c j : ℝ) : ℂ) • kapA (φ j : E →ₗ[ℂ] ℂ) (u - u0) := by
      simp only [a, ContinuousLinearMap.coe_smul, kapA, LinearMap.coe_comp, Function.comp_apply,
        TensorProduct.map_smul_left, LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe]
    rw [e1, map_smul, norm_smul, hgy, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (apply_nonneg _ _) (hc0 j).le)] at h1
    have h2 : α0 (e j) * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) (u - u0)) =
        c j * (α0 (e j) / c j * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) (u - u0))) := by
      field_simp [(hc0 j).ne']
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1.le (hc0 j).le
  have hk := key_est hE φ e hexp hα0 β0 (p k) hbil hc00 hsum (u - u0)
  have h3 : ∑' j, α0 (e j) * β0 (kapA (φ j : E →ₗ[ℂ] ℂ) (u - u0)) ≤ ∑' j, c j * δ :=
    (hsum _).tsum_le_tsum hj (hcs.mul_right δ)
  rw [tsum_mul_right] at h3
  calc p k (u - u0) ≤ c0 * ((∑' j, c j) * δ) := hk.trans (mul_le_mul_of_nonneg_left h3 hc00.le)
    _ = (c0 * ∑' j, c j) * δ := by ring
    _ < (c0 * ∑' j, c j + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := by
        show (c0 * ∑' j, c j + 1) * (ε / (c0 * ∑' j, c j + 1)) = ε
        field_simp

end nucframe

section nucthm

open MasulloGRH TensorProduct Bornology

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [τE : TopologicalSpace E]
variable {κE : Type u} {pE : SeminormFamily ℂ E κE} (hE : WithSeminorms pE)
variable {ι : Type*} (φ : ι → StrongDual ℂ E) (e : ι → E) (c : ι → ℝ)
variable (hexp : ∀ x, HasSum (fun j => φ j x • e j) x)
variable (hc0 : ∀ j, 0 < c j) (hcs : Summable c)
variable (hdom : ∀ P : Seminorm ℂ E, Continuous P → ∃ P' : Seminorm ℂ E, Continuous P' ∧
  ∀ j x, P (e j) * ‖φ j x‖ ≤ c j * P' x)

include hE hexp hc0 hcs hdom in
theorem nuclear_of_frame [T2Space E] : IsNuclear E := by
  refine ⟨⟨lc_of_ws hE, inferInstance⟩, fun F _ _ τF hF => ?_⟩
  obtain ⟨⟨κ, _, q, hq⟩, -⟩ := hF
  exact le_antisymm (proj_le_eps hE hq)
    (le_sInf fun t ht => eps_le_piF hE hq φ e c hexp hc0 hcs hdom t ht)

end nucthm

section ctvs

open MasulloGRH

lemma ctvs_of_complete {E : Type*} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
    [CompleteSpace E] [T2Space E] : IsCompleteTVS E := by
  refine ⟨inferInstance, fun f hf => ?_⟩
  obtain ⟨hne, hc⟩ := hf
  have hC : Cauchy f := by
    rw [cauchy_iff]
    refine ⟨hne, fun s hs => ?_⟩
    rw [uniformity_eq_comap_nhds_zero] at hs
    obtain ⟨U, hU, hUs⟩ := hs
    obtain ⟨A, hA, hAU⟩ := hc U hU
    refine ⟨A, hA, fun p hp => hUs ?_⟩
    exact hAU p.2 hp.2 p.1 hp.1
  exact CompleteSpace.complete hC

lemma sch_nuclear (m : ℕ) : IsNuclear (Sch m) := by
  refine nuclear_of_frame (schwartz_withSeminorms ℂ (V m) ℂ) (fun j => phiF j.1 j.2)
    (fun j => eF j.1 j.2) cw ?_ ?_ ?_ ?_
  · exact frame_hasSum
  · exact cw_pos
  · exact cw_summable
  · exact frame_dom

end ctvs

/-! ### the tensor map `𝓢(E) ⊗ 𝓢(F) → 𝓢(E × F)` -/

section tens

open MasulloGRH TensorProduct LineDeriv
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- the maximum of the Schwartz seminorms of index `≤ (K, L)` -/
def PS (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (K L : ℕ) : Seminorm ℂ 𝓢(X, ℂ) :=
  (Finset.Iic (K, L)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2)

lemma PS_cont (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (K L : ℕ) :
    Continuous (PS X K L) :=
  (schwartz_withSeminorms ℂ X ℂ).finset_sups.continuous_seminorm (Finset.Iic (K, L))

lemma le_PS {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {K L k l : ℕ} (hk : k ≤ K)
    (hl : l ≤ L) (f : 𝓢(X, ℂ)) : SchwartzMap.seminorm ℂ k l f ≤ PS X K L f := by
  have h : (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ (F := ℂ) (E := X) m.1 m.2) (k, l) ≤ PS X K L :=
    Finset.le_sup (f := fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ (F := ℂ) (E := X) m.1 m.2)
      (Finset.mem_Iic.2 (Prod.mk_le_mk.2 ⟨hk, hl⟩))
  exact h f

lemma PS_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {K L : ℕ} (f : 𝓢(X, ℂ)) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ k ≤ K, ∀ l ≤ L, SchwartzMap.seminorm ℂ k l f ≤ M) : PS X K L f ≤ M := by
  refine Seminorm.finset_sup_apply_le hM fun i hi => ?_
  have := Prod.mk_le_mk.1 (Finset.mem_Iic.1 hi)
  exact h i.1 this.1 i.2 this.2

lemma sn_le_PS {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (σ : Seminorm ℂ 𝓢(X, ℂ))
    (hσ : Continuous σ) : ∃ (C : ℝ) (K L : ℕ), 0 ≤ C ∧ ∀ f, σ f ≤ C * PS X K L f := by
  obtain ⟨s, C, -, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X ℂ) σ hσ
  refine ⟨C, (s.sup id).1, (s.sup id).2, C.2, fun f => ?_⟩
  have h1 := h f
  have h2 : s.sup (schwartzSeminormFamily ℂ X ℂ) ≤ PS X (s.sup id).1 (s.sup id).2 :=
    Finset.sup_mono fun i hi => Finset.mem_Iic.2 (Finset.le_sup (f := id) hi)
  have h3 := h2 f
  have e : (C • s.sup (schwartzSeminormFamily ℂ X ℂ)) f =
      (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ X ℂ)) f := by
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  rw [e] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h3 C.2)

lemma prod_bound (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) (k n : ℕ) (p : E × F) :
    ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun q : E × F => f q.1 * g q.2) p‖ ≤
      2 ^ n * 4 ^ k * (PS E k n f * PS F k n g) := by
  have hfs : ContDiff ℝ (n : WithTop ℕ∞) (f : E → ℂ) := (f.smooth ⊤).of_le (by exact_mod_cast le_top)
  have hgs : ContDiff ℝ (n : WithTop ℕ∞) (g : F → ℂ) := (g.smooth ⊤).of_le (by exact_mod_cast le_top)
  have hf : ContDiff ℝ (n : WithTop ℕ∞) (fun q : E × F => f q.1) := hfs.comp contDiff_fst
  have hg : ContDiff ℝ (n : WithTop ℕ∞) (fun q : E × F => g q.2) := hgs.comp contDiff_snd
  have hL := norm_iteratedFDeriv_mul_le hf hg p (le_refl _)
  have h1 : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun q : E × F => f q.1) p‖ ≤
      ‖iteratedFDeriv ℝ i f p.1‖ := by
    intro i hi
    have := (ContinuousLinearMap.fst ℝ E F).iteratedFDeriv_comp_right hfs p (i := i)
      (by exact_mod_cast hi)
    have e : (fun q : E × F => f q.1) = f ∘ (ContinuousLinearMap.fst ℝ E F) := rfl
    rw [e, this]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h' : ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ E F‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_fst_le ..)
    calc _ ≤ ‖iteratedFDeriv ℝ i f p.1‖ * 1 := mul_le_mul_of_nonneg_left h' (norm_nonneg _)
      _ = _ := mul_one _
  have h2 : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun q : E × F => g q.2) p‖ ≤
      ‖iteratedFDeriv ℝ i g p.2‖ := by
    intro i hi
    have := (ContinuousLinearMap.snd ℝ E F).iteratedFDeriv_comp_right hgs p (i := i)
      (by exact_mod_cast hi)
    have e : (fun q : E × F => g q.2) = g ∘ (ContinuousLinearMap.snd ℝ E F) := rfl
    rw [e, this]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h' : ∏ _j : Fin i, ‖ContinuousLinearMap.snd ℝ E F‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_snd_le ..)
    calc _ ≤ ‖iteratedFDeriv ℝ i g p.2‖ * 1 := mul_le_mul_of_nonneg_left h' (norm_nonneg _)
      _ = _ := mul_one _
  have hp : ‖p‖ ^ k ≤ (1 + ‖p.1‖) ^ k * (1 + ‖p.2‖) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ k
    rw [Prod.norm_def]
    have a := norm_nonneg p.1
    have b := norm_nonneg p.2
    refine max_le ?_ ?_ <;> nlinarith
  have hA := apply_nonneg (PS E k n) f
  have hB := apply_nonneg (PS F k n) g
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖p‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun q : E × F => f q.1) p‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun q : E × F => g q.2) p‖) ≤
      (n.choose i : ℝ) * (4 ^ k * (PS E k n f * PS F k n g)) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have a1 := h1 i hi'
    have a2 := h2 (n - i) (Nat.sub_le _ _)
    have b1 : (1 + ‖p.1‖) ^ k * ‖iteratedFDeriv ℝ i f p.1‖ ≤ 2 ^ k * PS E k n f :=
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) (le_refl _) hi' f p.1
    have b2 : (1 + ‖p.2‖) ^ k * ‖iteratedFDeriv ℝ (n - i) g p.2‖ ≤ 2 ^ k * PS F k n g :=
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) (le_refl _)
        (Nat.sub_le _ _) g p.2
    have c0 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    calc ‖p‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun q : E × F => f q.1) p‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun q : E × F => g q.2) p‖)
        ≤ ((1 + ‖p.1‖) ^ k * (1 + ‖p.2‖) ^ k) * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f p.1‖ *
          ‖iteratedFDeriv ℝ (n - i) g p.2‖) := by
          refine mul_le_mul hp ?_ (by positivity) (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left a1 c0) a2 (norm_nonneg _) (by positivity)
      _ = (n.choose i : ℝ) * (((1 + ‖p.1‖) ^ k * ‖iteratedFDeriv ℝ i f p.1‖) *
          ((1 + ‖p.2‖) ^ k * ‖iteratedFDeriv ℝ (n - i) g p.2‖)) := by ring
      _ ≤ (n.choose i : ℝ) * ((2 ^ k * PS E k n f) * (2 ^ k * PS F k n g)) := by
          refine mul_le_mul_of_nonneg_left ?_ c0
          exact mul_le_mul b1 b2 (by positivity) (by positivity)
      _ = (n.choose i : ℝ) * (4 ^ k * (PS E k n f * PS F k n g)) := by
          have : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
          rw [this]; ring
  calc ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun q : E × F => f q.1 * g q.2) p‖
      ≤ ‖p‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun q : E × F => f q.1) p‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun q : E × F => g q.2) p‖ :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), ‖p‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun q : E × F => f q.1) p‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun q : E × F => g q.2) p‖) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (4 ^ k * (PS E k n f * PS F k n g)) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ n * 4 ^ k * (PS E k n f * PS F k n g) := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]; ring

/-- the Schwartz function `(x, y) ↦ f x * g y` -/
def prodS (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) : 𝓢(E × F, ℂ) where
  toFun p := f p.1 * g p.2
  smooth' := ((f.smooth ⊤).comp contDiff_fst).mul ((g.smooth ⊤).comp contDiff_snd)
  decay' k n := ⟨_, fun p => prod_bound f g k n p⟩

@[simp] lemma prodS_apply (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) (p : E × F) :
    prodS f g p = f p.1 * g p.2 := rfl

lemma prodS_seminorm_le (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (prodS f g) ≤ 2 ^ n * 4 ^ k * (PS E k n f * PS F k n g) :=
  SchwartzMap.seminorm_le_bound ℂ k n _
    (mul_nonneg (by positivity) (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
    (prod_bound f g k n)

/-- `prodS` as a bilinear map -/
def prodBil : 𝓢(E, ℂ) →ₗ[ℂ] 𝓢(F, ℂ) →ₗ[ℂ] 𝓢(E × F, ℂ) :=
  LinearMap.mk₂ ℂ prodS
    (fun f₁ f₂ g => by ext p; simp [add_mul])
    (fun c f g => by ext p; simp [mul_assoc])
    (fun f g₁ g₂ => by ext p; simp [mul_add])
    (fun c f g => by ext p; simp [mul_left_comm])

/-- the canonical map `𝓢(E) ⊗ 𝓢(F) → 𝓢(E × F)` -/
def jT : 𝓢(E, ℂ) ⊗[ℂ] 𝓢(F, ℂ) →ₗ[ℂ] 𝓢(E × F, ℂ) := TensorProduct.lift prodBil

@[simp] lemma jT_tmul (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) : jT (f ⊗ₜ[ℂ] g) = prodS f g := by
  simp [jT, prodBil]

lemma prodS_zero_right (f : 𝓢(E, ℂ)) : prodS f (0 : 𝓢(F, ℂ)) = 0 := by ext p; simp

lemma prodS_zero_left (g : 𝓢(F, ℂ)) : prodS (0 : 𝓢(E, ℂ)) g = 0 := by ext p; simp

lemma prodS_cont : Continuous (fun p : 𝓢(E, ℂ) × 𝓢(F, ℂ) => prodS p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, y0⟩
  rw [ContinuousAt, (schwartz_withSeminorms ℂ (E × F) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  set σ := PS E k n
  set β := PS F k n
  have hσ : Continuous σ := PS_cont E k n
  have hβ : Continuous β := PS_cont F k n
  set c : ℝ := 2 ^ n * 4 ^ k
  let G : 𝓢(E, ℂ) × 𝓢(F, ℂ) → ℝ := fun p => c * (σ (p.1 - x0) * β (p.2 - y0)) +
    c * (σ x0 * β (p.2 - y0)) + c * (σ (p.1 - x0) * β y0)
  have hG : Continuous G := by
    have h1 : Continuous fun p : 𝓢(E, ℂ) × 𝓢(F, ℂ) => σ (p.1 - x0) :=
      hσ.comp (continuous_fst.sub continuous_const)
    have h2 : Continuous fun p : 𝓢(E, ℂ) × 𝓢(F, ℂ) => β (p.2 - y0) :=
      hβ.comp (continuous_snd.sub continuous_const)
    exact ((continuous_const.mul (h1.mul h2)).add
      (continuous_const.mul (continuous_const.mul h2))).add
      (continuous_const.mul (h1.mul continuous_const))
  have hG0 : G (x0, y0) = 0 := by simp [G]
  have hev := (hG.tendsto (x0, y0)).eventually
    (Iio_mem_nhds (show G (x0, y0) < ε by rw [hG0]; exact hε))
  filter_upwards [hev] with p hp
  show SchwartzMap.seminorm ℂ k n (prodS p.1 p.2 - prodS x0 y0) < ε
  have e : prodS p.1 p.2 - prodS x0 y0 =
      prodS (p.1 - x0) (p.2 - y0) + prodS x0 (p.2 - y0) + prodS (p.1 - x0) y0 := by
    ext q; simp; ring
  rw [e]
  have h1 := map_add_le_add (SchwartzMap.seminorm ℂ k n)
    (prodS (p.1 - x0) (p.2 - y0) + prodS x0 (p.2 - y0)) (prodS (p.1 - x0) y0)
  have h2 := map_add_le_add (SchwartzMap.seminorm ℂ k n)
    (prodS (p.1 - x0) (p.2 - y0)) (prodS x0 (p.2 - y0))
  have h3 := prodS_seminorm_le (p.1 - x0) (p.2 - y0) k n
  have h4 := prodS_seminorm_le x0 (p.2 - y0) k n
  have h5 := prodS_seminorm_le (p.1 - x0) y0 k n
  have hp' : G p < ε := hp
  simp only [G] at hp'
  linarith

lemma lineDeriv_prodS (w : E) (v : F) (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) :
    ∂_{((w, v) : E × F)} (prodS f g) = prodS (∂_{w} f) g + prodS f (∂_{v} g) := by
  ext p
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h1 : HasFDerivAt (fun q : E × F => f q.1)
      ((fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ E F)) p :=
    (f.hasFDerivAt p.1).comp p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : E × F => g q.2)
      ((fderiv ℝ g p.2).comp (ContinuousLinearMap.snd ℝ E F)) p :=
    (g.hasFDerivAt p.2).comp p hasFDerivAt_snd
  have h : HasFDerivAt (fun q : E × F => f q.1 * g q.2) _ p := h1.mul h2
  have e : ((prodS f g : 𝓢(E × F, ℂ)) : E × F → ℂ) = fun q => f q.1 * g q.2 := rfl
  rw [e, h.fderiv]
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

lemma iter_prodS_left {l : ℕ} (w : Fin l → E) (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) :
    ∂^{fun i => ((w i, 0) : E × F)} (prodS f g) = prodS (∂^{w} f) g := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left]
    have e : Fin.tail (fun i => ((w i, 0) : E × F)) = fun i => ((Fin.tail w i, 0) : E × F) := rfl
    rw [e, ih, lineDeriv_prodS, lineDerivOp_left_zero, prodS_zero_right, add_zero]

lemma iter_prodS_right {l : ℕ} (v : Fin l → F) (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) :
    ∂^{fun i => ((0, v i) : E × F)} (prodS f g) = prodS f (∂^{v} g) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left]
    have e : Fin.tail (fun i => ((0, v i) : E × F)) = fun i => ((0, Fin.tail v i) : E × F) := rfl
    rw [e, ih, lineDeriv_prodS, lineDerivOp_left_zero, prodS_zero_left, zero_add]

end tens

/-! ### iterated derivatives versus iterated line derivatives -/

section lined

open LineDeriv
open scoped SchwartzMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma nI_line (h : 𝓢(X, ℂ)) (v : X) (k : ℕ) (z : X) :
    ‖iteratedFDeriv ℝ k ((∂_{v} h : 𝓢(X, ℂ)) : X → ℂ) z‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (k + 1) h z‖ := by
  have e : ((∂_{v} h : 𝓢(X, ℂ)) : X → ℂ) =
      (ContinuousLinearMap.apply ℝ ℂ v) ∘ (fderiv ℝ h) := by
    ext y; simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hs : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (h : X → ℂ) :=
    (h.smooth ⊤).of_le (by exact_mod_cast le_top)
  have hd : ContDiffAt ℝ (k : WithTop ℕ∞) (fderiv ℝ h) z :=
    (hs.fderiv_right (m := k) (by norm_cast)).contDiffAt
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_left _ hd (le_refl _)]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have key := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := (h : X → ℂ)) (x := z) (n := k)
    (Fin.snoc (α := fun _ => X) m v)
  simp only [Fin.init_snoc, Fin.snoc_last] at key
  have e2 : ((ContinuousLinearMap.apply ℝ ℂ v).compContinuousMultilinearMap
      (iteratedFDeriv ℝ k (fderiv ℝ h) z)) m =
      iteratedFDeriv ℝ (k + 1) h z (Fin.snoc (α := fun _ => X) m v) := by
    rw [key]; rfl
  rw [e2]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  exact le_of_eq (by ring)

lemma nI_iter {l : ℕ} (m : Fin l → X) (h : 𝓢(X, ℂ)) (k : ℕ) (z : X) :
    ‖iteratedFDeriv ℝ k ((∂^{m} h : 𝓢(X, ℂ)) : X → ℂ) z‖ ≤
      (∏ i, ‖m i‖) * ‖iteratedFDeriv ℝ (k + l) h z‖ := by
  induction l generalizing k with
  | zero => simp
  | succ l ih =>
    rw [iteratedLineDerivOp_succ_left]
    refine (nI_line _ _ _ _).trans ?_
    have h1 := ih (Fin.tail m) (k + 1)
    have e : k + 1 + l = k + (l + 1) := by omega
    rw [e] at h1
    rw [Fin.prod_univ_succ, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

lemma nI_unit (h : 𝓢(X, ℂ)) (l : ℕ) (z : X) {c M : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M)
    (H : ∀ m : Fin l → X, (∀ i, ‖m i‖ ≤ 1) → c * ‖(∂^{m} h) z‖ ≤ M) :
    c * ‖iteratedFDeriv ℝ l h z‖ ≤ M := by
  rcases hc.eq_or_lt with hc0 | hc0
  · rw [← hc0, zero_mul]; exact hM
  rw [← le_div_iff₀' hc0]
  refine ContinuousMultilinearMap.opNorm_le_bound (div_nonneg hM hc) fun m => ?_
  by_cases h0 : ∃ i, m i = 0
  · obtain ⟨i, hi⟩ := h0
    rw [ContinuousMultilinearMap.map_coord_zero _ i hi, norm_zero]
    exact mul_nonneg (div_nonneg hM hc) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · push Not at h0
    let u : Fin l → X := fun i => (‖m i‖⁻¹) • m i
    have hu : ∀ i, ‖u i‖ ≤ 1 := fun i => by
      simp [u, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 (h0 i))]
    have hm : m = fun i => ‖m i‖ • u i := by
      funext i
      simp [u, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 (h0 i))]
    have hH := H u hu
    rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv] at hH
    have hD : ‖iteratedFDeriv ℝ l h z u‖ ≤ M / c := by rw [le_div_iff₀' hc0]; exact hH
    have e : iteratedFDeriv ℝ l h z m = (∏ i, ‖m i‖) • iteratedFDeriv ℝ l h z u := by
      conv_lhs => rw [hm]
      exact ContinuousMultilinearMap.map_smul_univ _ _ _
    rw [e, norm_smul, norm_prod]
    simp only [norm_norm]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hD (Finset.prod_nonneg fun _ _ => norm_nonneg _)

end lined

/-! ### the kernel estimate -/

section kern

open MasulloGRH TensorProduct LineDeriv
open scoped SchwartzMap

def kapB {V G : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup G] [Module ℂ G]
    (b : G →ₗ[ℂ] ℂ) : V ⊗[ℂ] G →ₗ[ℂ] V :=
  (TensorProduct.rid ℂ V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id b

@[simp] lemma kapB_tmul {V G : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup G] [Module ℂ G]
    (b : G →ₗ[ℂ] ℂ) (x : V) (y : G) : kapB b (x ⊗ₜ[ℂ] y) = b y • x := by
  simp [kapB]

lemma swap_kap {V G : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup G] [Module ℂ G]
    (a : V →ₗ[ℂ] ℂ) (b : G →ₗ[ℂ] ℂ) (t : V ⊗[ℂ] G) : b (kapA a t) = a (kapB b t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [mul_comm]
  | add u v hu hv => simp [map_add, hu, hv]

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- evaluation of an iterated line derivative at a point -/
def devL {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (y : X) {l : ℕ} (m : Fin l → X) :
    𝓢(X, ℂ) →ₗ[ℂ] ℂ where
  toFun g := (∂^{m} g) y
  map_add' g₁ g₂ := by rw [iteratedLineDerivOp_add]; rfl
  map_smul' c g := by rw [iteratedLineDerivOp_smul]; rfl

lemma devL_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (y : X) {l : ℕ}
    (m : Fin l → X) (g : 𝓢(X, ℂ)) : devL y m g = (∂^{m} g) y := rfl

lemma kid (t : 𝓢(E, ℂ) ⊗[ℂ] 𝓢(F, ℂ)) (x : E) (y : F) {l' l : ℕ} (w : Fin l' → E)
    (m : Fin l → F) :
    (∂^{w} (kapB (devL y m) t)) x =
      (∂^{fun i => ((w i, 0) : E × F)} (∂^{fun i => ((0, m i) : E × F)} (jT t))) (x, y) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [iteratedLineDerivOp_zero]
  | tmul f g =>
    rw [kapB_tmul, jT_tmul, iter_prodS_right, iter_prodS_left, iteratedLineDerivOp_smul]
    simp [devL_apply, mul_comm]
  | add u v hu hv =>
    rw [map_add, map_add, iteratedLineDerivOp_add, iteratedLineDerivOp_add,
      iteratedLineDerivOp_add]
    simp [hu, hv]

lemma kernel_bound (a : 𝓢(E, ℂ) →ₗ[ℂ] ℂ) (b : 𝓢(F, ℂ) →ₗ[ℂ] ℂ) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) {K1 L1 K2 L2 : ℕ} (ha : ∀ f, ‖a f‖ ≤ C₁ * PS E K1 L1 f)
    (hb : ∀ g, ‖b g‖ ≤ C₂ * PS F K2 L2 g) (t : 𝓢(E, ℂ) ⊗[ℂ] 𝓢(F, ℂ)) :
    ‖b (kapA a t)‖ ≤ C₂ * (C₁ * PS (E × F) (K1 + K2) (L1 + L2) (jT t)) := by
  set T := PS (E × F) (K1 + K2) (L1 + L2) (jT t) with hTdef
  have hT : 0 ≤ T := apply_nonneg _ _
  have core : ∀ k ≤ K2, ∀ l ≤ L2, ∀ k' ≤ K1, ∀ l' ≤ L1, ∀ (x : E) (y : F) (w : Fin l' → E)
      (m : Fin l → F), (∀ i, ‖w i‖ ≤ 1) → (∀ i, ‖m i‖ ≤ 1) →
      ‖x‖ ^ k' * ‖y‖ ^ k * ‖(∂^{w} (kapB (devL y m) t)) x‖ ≤ T := by
    intro k hk l hl k' hk' l' hl' x y w m hw hm
    rw [kid, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    set U := ∂^{fun i => ((0, m i) : E × F)} (jT t)
    have hw' : ∏ i, ‖((w i, 0) : E × F)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => by
        simpa [Prod.norm_mk] using hw i)
    have hm' : ∏ i, ‖((0, m i) : E × F)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => by
        simpa [Prod.norm_mk] using hm i)
    have s1 : ‖iteratedFDeriv ℝ l' U (x, y) (fun i => ((w i, 0) : E × F))‖ ≤
        ‖iteratedFDeriv ℝ l' U (x, y)‖ :=
      (ContinuousMultilinearMap.le_opNorm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hw')
    have s2 : ‖iteratedFDeriv ℝ l' U (x, y)‖ ≤ ‖iteratedFDeriv ℝ (l' + l) (jT t) (x, y)‖ :=
      (nI_iter _ (jT t) l' (x, y)).trans (mul_le_of_le_one_left (norm_nonneg _) hm')
    have s3 : ‖x‖ ^ k' * ‖y‖ ^ k ≤ ‖((x, y) : E × F)‖ ^ (k' + k) := by
      rw [pow_add, Prod.norm_mk]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _)
        (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _) (by positivity) (by positivity)
    calc ‖x‖ ^ k' * ‖y‖ ^ k * ‖iteratedFDeriv ℝ l' U (x, y) (fun i => ((w i, 0) : E × F))‖
        ≤ ‖((x, y) : E × F)‖ ^ (k' + k) * ‖iteratedFDeriv ℝ (l' + l) (jT t) (x, y)‖ :=
          mul_le_mul s3 (s1.trans s2) (norm_nonneg _) (by positivity)
      _ ≤ SchwartzMap.seminorm ℂ (k' + k) (l' + l) (jT t) := SchwartzMap.le_seminorm ℂ _ _ _ _
      _ ≤ T := le_PS (by omega) (by omega) _
  have step1 : ∀ k ≤ K2, ∀ l ≤ L2, ∀ (y : F) (m : Fin l → F), (∀ i, ‖m i‖ ≤ 1) →
      ‖y‖ ^ k * ‖(∂^{m} (kapA a t)) y‖ ≤ C₁ * T := by
    intro k hk l hl y m hm
    have e : (∂^{m} (kapA a t)) y = a (kapB (devL y m) t) := swap_kap a (devL y m) t
    rw [e]
    set S := kapB (devL y m) t
    have hS : ‖y‖ ^ k * PS E K1 L1 S ≤ T := by
      rcases (pow_nonneg (norm_nonneg y) k).eq_or_lt with h0 | h0
      · rw [← h0, zero_mul]; exact hT
      rw [← le_div_iff₀' h0]
      refine PS_le _ (div_nonneg hT h0.le) fun k' hk' l' hl' => ?_
      refine SchwartzMap.seminorm_le_bound ℂ k' l' _ (div_nonneg hT h0.le) fun x => ?_
      rw [le_div_iff₀' h0, ← mul_assoc]
      refine nI_unit S l' x (by positivity) hT fun w hw => ?_
      have := core k hk l hl k' hk' l' hl' x y w m hw hm
      rwa [mul_comm (‖x‖ ^ k') (‖y‖ ^ k)] at this
    calc ‖y‖ ^ k * ‖a S‖ ≤ ‖y‖ ^ k * (C₁ * PS E K1 L1 S) :=
          mul_le_mul_of_nonneg_left (ha S) (by positivity)
      _ = C₁ * (‖y‖ ^ k * PS E K1 L1 S) := by ring
      _ ≤ C₁ * T := mul_le_mul_of_nonneg_left hS hC₁
  have step2 : PS F K2 L2 (kapA a t) ≤ C₁ * T := by
    refine PS_le _ (mul_nonneg hC₁ hT) fun k hk l hl => ?_
    refine SchwartzMap.seminorm_le_bound ℂ k l _ (mul_nonneg hC₁ hT) fun y => ?_
    exact nI_unit _ l y (by positivity) (mul_nonneg hC₁ hT) fun m hm => step1 k hk l hl y m hm
  exact (hb _).trans (mul_le_mul_of_nonneg_left step2 hC₂)

lemma induced_le_eps :
    TopologicalSpace.induced (jT : 𝓢(E, ℂ) ⊗[ℂ] 𝓢(F, ℂ) →ₗ[ℂ] 𝓢(E × F, ℂ)) inferInstance ≤
      epsTensorTopology 𝓢(E, ℂ) 𝓢(F, ℂ) := by
  letI t : TopologicalSpace (𝓢(E, ℂ) ⊗[ℂ] 𝓢(F, ℂ)) :=
    TopologicalSpace.induced (jT : 𝓢(E, ℂ) ⊗[ℂ] 𝓢(F, ℂ) →ₗ[ℂ] 𝓢(E × F, ℂ)) inferInstance
  show t ≤ epsTensorTopology 𝓢(E, ℂ) 𝓢(F, ℂ)
  rw [epsTensorTopology, ← continuous_iff_le_induced, continuous_iff_continuousAt]
  intro u0
  rw [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  rintro S ⟨A, B, hA, hB, rfl⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨σ, hσ, hσA⟩ := eqc_bound (schwartz_withSeminorms ℂ E ℂ) hA
  obtain ⟨β, hβ, hβB⟩ := eqc_bound (schwartz_withSeminorms ℂ F ℂ) hB
  obtain ⟨C₁, K1, L1, hC₁, h1⟩ := sn_le_PS σ hσ
  obtain ⟨C₂, K2, L2, hC₂, h2⟩ := sn_le_PS β hβ
  have hc : Continuous fun v : 𝓢(E × F, ℂ) =>
      C₂ * (C₁ * PS (E × F) (K1 + K2) (L1 + L2) (v - jT u0)) :=
    continuous_const.mul (continuous_const.mul
      ((PS_cont _ _ _).comp (continuous_id.sub continuous_const)))
  have hev0 := (hc.tendsto (jT u0)).eventually
    (Iio_mem_nhds (show C₂ * (C₁ * PS (E × F) (K1 + K2) (L1 + L2) (jT u0 - jT u0)) < ε by
      simpa using hε))
  have hev : ∀ᶠ u in 𝓝 u0,
      C₂ * (C₁ * PS (E × F) (K1 + K2) (L1 + L2) (jT u - jT u0)) < ε := by
    have hn : 𝓝 u0 = Filter.comap (jT : 𝓢(E, ℂ) ⊗[ℂ] 𝓢(F, ℂ) →ₗ[ℂ] 𝓢(E × F, ℂ)) (𝓝 (jT u0)) :=
      nhds_induced _ u0
    rw [hn]; exact hev0.comap jT
  filter_upwards [hev] with u hu
  intro ab hab
  change dist (tensorFunctional _ _ ab u0) (tensorFunctional _ _ ab u) < ε
  rw [dist_eq_norm, norm_sub_rev, ← tf_sub]
  obtain ⟨a, b⟩ := ab
  rw [tf_kapA]
  refine lt_of_le_of_lt (kernel_bound (a : 𝓢(E, ℂ) →ₗ[ℂ] ℂ) (b : 𝓢(F, ℂ) →ₗ[ℂ] ℂ) hC₁ hC₂
    (fun f => (hσA a hab.1 f).trans (h1 f)) (fun g => (hβB b hab.2 g).trans (h2 g)) (u - u0)) ?_
  rwa [map_sub]

/-- evaluation at a point -/
def evS {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (z : X) : 𝓢(X, ℂ) →ₗ[ℂ] ℂ where
  toFun g := g z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma evS_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (z : X)
    (g : 𝓢(X, ℂ)) : evS z g = g z := rfl

lemma jT_injective :
    Function.Injective (jT : 𝓢(E, ℂ) ⊗[ℂ] 𝓢(F, ℂ) →ₗ[ℂ] 𝓢(E × F, ℂ)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro t ht
  let bs := Module.Basis.ofVectorSpace ℂ 𝓢(E, ℂ)
  let φ := TensorProduct.equivFinsuppOfBasisLeft (N := 𝓢(F, ℂ)) bs
  have ht' : t = (φ t).sum fun i g => bs i ⊗ₜ[ℂ] g := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hz : φ t = 0 := by
    ext i y
    let c : _ →₀ ℂ := (φ t).mapRange (fun g : 𝓢(F, ℂ) => g y) rfl
    have hc : Finsupp.linearCombination ℂ bs c = 0 := by
      ext x
      have h1 : evS (x, y) (jT ((φ t).sum fun i g => bs i ⊗ₜ[ℂ] g)) = 0 := by
        rw [← ht', ht]; rfl
      rw [Finsupp.sum, map_sum, map_sum] at h1
      have h2 : Finsupp.linearCombination ℂ bs c x =
          evS x ((φ t).sum fun i g => g y • bs i) := by
        rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
        rfl
      rw [h2, Finsupp.sum, map_sum]
      show _ = (0 : ℂ)
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [mul_comm]
    have h3 := linearIndependent_iff.1 bs.linearIndependent c hc
    have h4 := DFunLike.congr_fun h3 i
    simpa [c] using h4
  exact (LinearEquiv.map_eq_zero_iff φ).1 hz

end kern

/-! ### density of the tensors -/

section dense

open MasulloGRH TensorProduct
open scoped SchwartzMap

variable (m n : ℕ)

/-- `ℝ^m × ℝ^n ≃ ℝ^(m+n)` -/
def splitE : (V m × V n) ≃ₗ[ℝ] V (m + n) where
  toFun p := WithLp.toLp 2 (Fin.append (fun i => p.1 i) (fun i => p.2 i))
  map_add' p q := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' c p := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  invFun z := (WithLp.toLp 2 fun i => z (Fin.castAdd n i), WithLp.toLp 2 fun i => z (Fin.natAdd m i))
  left_inv p := by
    ext i <;> simp
  right_inv z := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

def splitCLE : (V m × V n) ≃L[ℝ] V (m + n) := (splitE m n).toContinuousLinearEquiv

@[simp] lemma splitCLE_left (p : V m × V n) (i : Fin m) :
    splitCLE m n p (Fin.castAdd n i) = p.1 i := by
  simp [splitCLE, splitE]

@[simp] lemma splitCLE_right (p : V m × V n) (i : Fin n) :
    splitCLE m n p (Fin.natAdd m i) = p.2 i := by
  simp [splitCLE, splitE]

lemma ech_add (s t : ℝ) : ech (s + t) = ech s * ech t := by
  rw [ech, ech, ech, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eF_split (N Ξ : Fin (m + n) → ℤ) (p : V m × V n) :
    eF N Ξ (splitCLE m n p) =
      eF (fun i => N (Fin.castAdd n i)) (fun i => Ξ (Fin.castAdd n i)) p.1 *
      eF (fun i => N (Fin.natAdd m i)) (fun i => Ξ (Fin.natAdd m i)) p.2 := by
  simp only [eF_apply, thtC, tht, inner_wlat, Fin.prod_univ_add, Fin.sum_univ_add, ech_add,
    PiLp.sub_apply, vlat_apply, splitCLE_left, splitCLE_right]
  push_cast
  ring

lemma jT_dense :
    DenseRange (jT : 𝓢(V m, ℂ) ⊗[ℂ] 𝓢(V n, ℂ) →ₗ[ℂ] 𝓢(V m × V n, ℂ)) := by
  intro u
  let Φ : 𝓢(V (m + n), ℂ) →L[ℂ] 𝓢(V m × V n, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitCLE m n)
  let f : Sch (m + n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitCLE m n).symm u
  have hf : Φ f = u := by
    ext p
    show u ((splitCLE m n).symm (splitCLE m n p)) = u p
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hs := (frame_hasSum f).mapL Φ
  rw [hf] at hs
  have hmem : ∀ b : (Fin (m + n) → ℤ) × (Fin (m + n) → ℤ),
      Φ (phiF b.1 b.2 f • eF b.1 b.2) ∈ LinearMap.range
        (jT : 𝓢(V m, ℂ) ⊗[ℂ] 𝓢(V n, ℂ) →ₗ[ℂ] 𝓢(V m × V n, ℂ)) := by
    intro b
    refine ⟨phiF b.1 b.2 f • (eF (fun i => b.1 (Fin.castAdd n i)) (fun i => b.2 (Fin.castAdd n i))
      ⊗ₜ[ℂ] eF (fun i => b.1 (Fin.natAdd m i)) (fun i => b.2 (Fin.natAdd m i))), ?_⟩
    rw [map_smul, map_smul, jT_tmul]
    congr 1
    ext p
    exact (eF_split m n b.1 b.2 p).symm
  refine mem_closure_of_tendsto hs (Filter.Eventually.of_forall fun s => ?_)
  exact Submodule.sum_mem _ fun b _ => hmem b

end dense

end

end MasulloGRHSchwartzKernelAux

open MasulloGRH TensorProduct Topology Filter MasulloGRHSchwartzKernelAux in
open scoped SchwartzMap in
theorem solution (m n : ℕ) :
    ∃ j : 𝓢(EuclideanSpace ℝ (Fin m), ℂ) ⊗[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →ₗ[ℂ]
        𝓢(EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n), ℂ),
      (∀ (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
          (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
          j (f ⊗ₜ[ℂ] g) p = f p.1 * g p.2) ∧
        IsCompletedProjTensor 𝓢(EuclideanSpace ℝ (Fin m), ℂ) 𝓢(EuclideanSpace ℝ (Fin n), ℂ) j := by
  refine ⟨jT, fun f g p => by rw [jT_tmul]; rfl, ?_⟩
  refine ⟨⟨lc_of_ws (schwartz_withSeminorms ℂ _ ℂ), inferInstance⟩, ctvs_of_complete,
    jT_injective, ?_, jT_dense m n⟩
  apply le_antisymm
  · refine sInf_le ⟨⟨ℕ × ℕ, inferInstance, _,
      LinearMap.withSeminorms_induced (schwartz_withSeminorms ℂ _ ℂ) jT⟩, ?_⟩
    rw [continuous_induced_rng]
    have h := prodS_cont (E := EuclideanSpace ℝ (Fin m)) (F := EuclideanSpace ℝ (Fin n))
    refine h.congr fun p => ?_
    simp
  · have hn : IsHLCS 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
      ⟨lc_of_ws (schwartz_withSeminorms ℂ _ ℂ), inferInstance⟩
    rw [(sch_nuclear m).2 _ hn]
    exact induced_le_eps
