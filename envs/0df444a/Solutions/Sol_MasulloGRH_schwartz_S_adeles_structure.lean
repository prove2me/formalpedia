-- Prove2me | solution 1 for MasulloGRH.schwartz_S_adeles_structure
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T09:40:02.520907+00:00
-- url     : https://prove2.me/submissions/e7a727e6-3030-4728-81e7-f2f56aecf65f

import Definitions.Def_MasulloGRH_ThetaSpaces

set_option autoImplicit false
set_option linter.all false

universe u

namespace Aux_SEN

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
  have h := Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (V m) ℂ) (x := f) hmem
  rw [SchwartzMap.schwartzSeminormFamily_apply] at h
  exact h

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
  have hc := Summable.mul_of_nonneg (f := fun n : Fin m → ℤ => ((1 + ‖vlat n‖) ^ (2 * m))⁻¹)
    (g := fun n : Fin m → ℤ => ((1 + ‖wlat n‖) ^ (2 * m))⁻¹) ha hb (fun n => by positivity)
    (fun n => by positivity)
  exact hc

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
    have hc : Summable (fun j : (Fin m → ℤ) × (Fin m → ℤ) => cw j * P' f) :=
      (cw_summable (m := m)).mul_right (P' f)
    refine Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) (fun j => ?_) hc
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

/-! ### the strong dual: seminorms and the dual frame -/

section sdual

open MasulloGRH TensorProduct Bornology

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

lemma bdd_clm (g : StrongDual ℂ E) {S : Set E} (hS : IsVonNBounded ℂ S) :
    ∃ R : ℝ, ∀ x ∈ S, ‖g x‖ ≤ R := by
  have hc : Continuous ((normSeminorm ℂ ℂ).comp (g : E →ₗ[ℂ] ℂ)) := by
    have : ((normSeminorm ℂ ℂ).comp (g : E →ₗ[ℂ] ℂ) : E → ℝ) = fun x => ‖g x‖ := by
      funext x; rfl
    rw [this]
    exact continuous_norm.comp g.continuous
  obtain ⟨R, hR⟩ := bdd_of_cont hc hS
  exact ⟨R, fun x hx => hR x hx⟩

/-- bounded subsets -/
abbrev BI (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Type u :=
  {B : Set E // IsVonNBounded ℂ B}

def evL (x : E) : StrongDual ℂ E →ₗ[ℂ] ℂ where
  toFun T := T x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- the strong dual seminorm `sup_{x ∈ B} |T x|` -/
def dsn (B : BI E) : Seminorm ℂ (StrongDual ℂ E) := ⨆ x : B.1, (normSeminorm ℂ ℂ).comp (evL (x : E))

lemma dsn_bdd (B : BI E) :
    BddAbove (Set.range fun x : B.1 => (normSeminorm ℂ ℂ).comp (evL (E := E) (x : E))) := by
  rw [Seminorm.bddAbove_range_iff]
  intro T
  obtain ⟨R, hR⟩ := bdd_clm T B.2
  exact ⟨R, by rintro _ ⟨x, rfl⟩; exact hR x x.2⟩

lemma dsn_apply (B : BI E) (T : StrongDual ℂ E) : dsn B T = ⨆ x : B.1, ‖T x‖ := by
  rw [dsn, Seminorm.iSup_apply (dsn_bdd B)]
  rfl

lemma le_dsn (B : BI E) (T : StrongDual ℂ E) {x : E} (hx : x ∈ B.1) : ‖T x‖ ≤ dsn B T := by
  have h := dsn_bdd B
  rw [Seminorm.bddAbove_range_iff] at h
  rw [dsn_apply]
  exact le_ciSup (h T) (⟨x, hx⟩ : B.1)

lemma dsn_le (B : BI E) (T : StrongDual ℂ E) {M : ℝ} (hM0 : 0 ≤ M) (h : ∀ x ∈ B.1, ‖T x‖ ≤ M) :
    dsn B T ≤ M := by
  rw [dsn_apply]
  exact Real.iSup_le (fun x => h x x.2) hM0

lemma bU_bdd (s : Finset (BI E)) : IsVonNBounded ℂ (⋃ B ∈ s, B.1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact a.2.union ih

def bU (s : Finset (BI E)) : BI E := ⟨⋃ B ∈ s, B.1, bU_bdd s⟩

lemma sup_dsn_le (s : Finset (BI E)) (T : StrongDual ℂ E) : (s.sup dsn) T ≤ dsn (bU s) T :=
  Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun B hB =>
    dsn_le B T (apply_nonneg _ _) fun x hx =>
      le_dsn (bU s) T (Set.mem_biUnion hB hx)

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]

lemma dws : WithSeminorms (dsn (E := E)) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  apply le_antisymm
  · refine le_iInf fun B => ?_
    rw [← tendsto_iff_comap, Metric.tendsto_nhds]
    intro ε hε
    have hN : {T : StrongDual ℂ E | ∀ y ∈ B.1, T y ∈ Metric.closedBall (0 : ℂ) (ε / 2)}
        ∈ 𝓝 (0 : StrongDual ℂ E) :=
      (ContinuousLinearMap.hasBasis_nhds_zero).mem_of_mem
        (i := (B.1, Metric.closedBall (0 : ℂ) (ε / 2)))
        ⟨B.2, Metric.closedBall_mem_nhds _ (half_pos hε)⟩
    filter_upwards [hN] with T hT
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
    refine lt_of_le_of_lt (dsn_le B T (by positivity) fun x hx => ?_) (half_lt_self hε)
    have := hT x hx
    rwa [mem_closedBall_zero_iff] at this
  · refine (ContinuousLinearMap.hasBasis_nhds_zero).ge_iff.2 ?_
    rintro ⟨B, U⟩ ⟨hB, hU⟩
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    refine mem_iInf_of_mem (⟨B, hB⟩ : BI E) (mem_comap.2 ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩)
    intro T hT x hx
    apply hεU
    rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (apply_nonneg _ _)] at hT
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (le_dsn ⟨B, hB⟩ T hx) hT

lemma dsn_cont (B : BI E) : Continuous (dsn B) := dws.continuous_seminorm B

/-- evaluation at a point as an element of the bidual -/
def evl (y : E) : StrongDual ℂ (StrongDual ℂ E) :=
  ⟨evL y, continuous_eval_const y⟩

@[simp] lemma evl_apply (y : E) (g : StrongDual ℂ E) : evl y g = g y := rfl

/-- a family of functionals uniformly bounded on bounded sets is bounded in the strong dual -/
lemma dual_bdd_of {A : Set (StrongDual ℂ E)}
    (h : ∀ B : BI E, ∃ M, ∀ g ∈ A, ∀ x ∈ B.1, ‖g x‖ ≤ M) : IsVonNBounded ℂ A := by
  rw [dws.isVonNBounded_iff_seminorm_bounded]
  intro B
  obtain ⟨M, hM⟩ := h B
  refine ⟨max M 0 + 1, by positivity, fun g hg => ?_⟩
  refine lt_of_le_of_lt ?_ (lt_add_one _)
  exact dsn_le B g (le_max_right _ _) fun x hx => (hM g hg x hx).trans (le_max_left _ _)

end sdual

section dframe

open MasulloGRH TensorProduct Bornology

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable {κE : Type*} {pE : SeminormFamily ℂ E κE} (hE : WithSeminorms pE)
variable {ι : Type*} (φ : ι → StrongDual ℂ E) (e : ι → E) (c : ι → ℝ)
variable (hexp : ∀ x, HasSum (fun j => φ j x • e j) x)
variable (hc0 : ∀ j, 0 < c j) (hcs : Summable c)
variable (hdom : ∀ P : Seminorm ℂ E, Continuous P → ∃ P' : Seminorm ℂ E, Continuous P' ∧
  ∀ j x, P (e j) * ‖φ j x‖ ≤ c j * P' x)

include hE hexp hc0 hcs hdom in
lemma dexp (T : StrongDual ℂ E) : HasSum (fun j => T (e j) • φ j) T := by
  classical
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hE ((normSeminorm ℂ ℂ).comp (T : E →ₗ[ℂ] ℂ))
    (continuous_norm.comp T.continuous)
  obtain ⟨P', hP', hdP⟩ := hdom (s.sup pE) (hE.finset_sups.continuous_seminorm s)
  have hTx : ∀ x, ‖T x‖ ≤ C * (s.sup pE) x := fun x => by
    have := hC x
    rwa [smul_apply, NNReal.smul_def, smul_eq_mul] at this
  -- termwise bound
  have hterm : ∀ j x, ‖φ j x * T (e j)‖ ≤ C * (c j * P' x) := by
    intro j x
    rw [norm_mul, mul_comm]
    calc ‖T (e j)‖ * ‖φ j x‖ ≤ C * (s.sup pE) (e j) * ‖φ j x‖ :=
          mul_le_mul_of_nonneg_right (hTx _) (norm_nonneg _)
      _ = C * ((s.sup pE) (e j) * ‖φ j x‖) := by ring
      _ ≤ C * (c j * P' x) := mul_le_mul_of_nonneg_left (hdP j x) C.2
  unfold HasSum
  rw [(dws (E := E)).tendsto_nhds _ T]
  intro B ε hε
  obtain ⟨M, hM⟩ := bdd_of_cont hP' B.2
  have hMc : Tendsto (fun J : Finset ι => ∑' j : ↥((J : Set ι)ᶜ), c j) atTop (𝓝 0) :=
    tendsto_tsum_compl_atTop_zero c
  have hδ : 0 < ε / (2 * ((C : ℝ) * max M 0 + 1)) := by positivity
  filter_upwards [hMc.eventually (Iio_mem_nhds hδ)] with J hJ
  refine lt_of_le_of_lt (dsn_le B _ (by positivity) fun x hx => ?_) (half_lt_self hε)
  -- the value at `x`
  have hsx : HasSum (fun j => φ j x * T (e j)) (T x) := by
    have := T.hasSum (hexp x)
    simpa [map_smul, smul_eq_mul] using this
  have hsumm : Summable fun j => ‖φ j x * T (e j)‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (hterm · x) ((hcs.mul_right _).mul_left _)
  have e1 : (∑ j ∈ J, T (e j) • φ j - T) x = -∑' j : ↥((J : Set ι)ᶜ), φ j x * T (e j) := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, ← hsx.tsum_eq,
      ← hsx.summable.sum_add_tsum_compl (s := J)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun j _ => mul_comm (T (e j)) (φ j x)]
    simp
  rw [e1, norm_neg]
  have hcomp : Summable fun j : ↥((J : Set ι)ᶜ) => c j := hcs.subtype _
  calc ‖∑' j : ↥((J : Set ι)ᶜ), φ j x * T (e j)‖
      ≤ ∑' j : ↥((J : Set ι)ᶜ), ‖φ j x * T (e j)‖ := norm_tsum_le_tsum_norm (hsumm.subtype _)
    _ ≤ ∑' j : ↥((J : Set ι)ᶜ), C * (c j * max M 0) :=
        (hsumm.subtype _).tsum_le_tsum (fun j => (hterm j x).trans
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((hM x hx).trans (le_max_left _ _))
            (hc0 _).le) C.2)) ((hcomp.mul_right _).mul_left _)
    _ = (C * max M 0) * ∑' j : ↥((J : Set ι)ᶜ), c j := by
        rw [← tsum_mul_left]; congr 1; funext j; ring
    _ ≤ (C * max M 0) * (ε / (2 * ((C : ℝ) * max M 0 + 1))) :=
        mul_le_mul_of_nonneg_left hJ.le (by positivity)
    _ ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_nonneg C.2 (le_max_right M 0)]

include hE hdom hc0 in
lemma ddom (P : Seminorm ℂ (StrongDual ℂ E)) (hP : Continuous P) :
    ∃ P' : Seminorm ℂ (StrongDual ℂ E), Continuous P' ∧
      ∀ j T, P (φ j) * ‖evl (e j) T‖ ≤ c j * P' T := by
  classical
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (dws (E := E)) P hP
  let Bs := bU s
  let B' : Set E := Set.range fun z : ι × Bs.1 => ((φ z.1 z.2 / c z.1 : ℂ)) • e z.1
  have hB' : IsVonNBounded ℂ B' := by
    rw [hE.isVonNBounded_iff_seminorm_bounded]
    intro I
    obtain ⟨P', hP', hdP⟩ := hdom (pE I) (hE.continuous_seminorm I)
    obtain ⟨M, hM⟩ := bdd_of_cont hP' Bs.2
    refine ⟨max M 0 + 1, by positivity, ?_⟩
    rintro _ ⟨⟨j, x⟩, rfl⟩
    refine lt_of_le_of_lt ?_ (lt_add_one _)
    rw [map_smul_eq_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc0 j),
      div_mul_eq_mul_div, div_le_iff₀ (hc0 j), mul_comm]
    calc (pE I) (e j) * ‖φ j x‖ ≤ c j * P' x := hdP j x
      _ ≤ c j * max M 0 := mul_le_mul_of_nonneg_left ((hM x x.2).trans (le_max_left _ _)) (hc0 j).le
      _ = max M 0 * c j := mul_comm _ _
  let B'' : BI E := ⟨B', hB'⟩
  refine ⟨(C : NNReal) • dsn B'', ?_, fun j T => ?_⟩
  · rw [FunLike.coe_smul]; exact (dsn_cont B'').const_smul _
  · rw [smul_apply, NNReal.smul_def, smul_eq_mul, evl_apply]
    have h1 : P (φ j) ≤ C * dsn Bs (φ j) := by
      have := hC (φ j)
      rw [smul_apply, NNReal.smul_def, smul_eq_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_left (sup_dsn_le s _) C.2)
    have h2 : dsn Bs (φ j) * ‖T (e j)‖ ≤ c j * dsn B'' T := by
      have h3 : dsn Bs (((‖T (e j)‖ : ℝ) : ℂ) • φ j) ≤ c j * dsn B'' T := by
        refine dsn_le Bs _ (mul_nonneg (hc0 j).le (apply_nonneg _ _)) fun x hx => ?_
        have hx' := le_dsn B'' T (x := ((φ j x / c j : ℂ)) • e j) ⟨(j, ⟨x, hx⟩), rfl⟩
        rw [map_smul, smul_eq_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hc0 j)] at hx'
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)]
        rw [div_mul_eq_mul_div, div_le_iff₀ (hc0 j)] at hx'
        linarith [mul_comm ‖T (e j)‖ ‖φ j x‖, mul_comm (c j) (dsn B'' T)]
      rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h3
      linarith [mul_comm (dsn Bs (φ j)) ‖T (e j)‖]
    calc P (φ j) * ‖T (e j)‖ ≤ C * dsn Bs (φ j) * ‖T (e j)‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = C * (dsn Bs (φ j) * ‖T (e j)‖) := by ring
      _ ≤ C * (c j * dsn B'' T) := mul_le_mul_of_nonneg_left h2 C.2
      _ = c j * (C * dsn B'' T) := by ring

include hE hexp hc0 hcs hdom in
theorem dual_nuclear_of_frame [T2Space (StrongDual ℂ E)] : IsNuclear (StrongDual ℂ E) :=
  nuclear_of_frame (dws (E := E)) (fun j => evl (e j)) φ c (dexp hE φ e c hexp hc0 hcs hdom) hc0 hcs
    (ddom hE φ e c hc0 hdom)

end dframe

/-! ### reflexivity and the Montel property of the strong dual -/

section barrel

open MasulloGRH Bornology

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

lemma barrel_bound [BarrelledSpace ℂ E] [ContinuousSMul ℂ E] {C : Set (StrongDual ℂ E)}
    (hC : IsVonNBounded ℂ C) :
    ∃ P : Seminorm ℂ E, Continuous P ∧ ∀ g ∈ C, ∀ v, ‖g v‖ ≤ P v := by
  let q : C → Seminorm ℂ E := fun g => (normSeminorm ℂ ℂ).comp ((g : StrongDual ℂ E) : E →ₗ[ℂ] ℂ)
  have hq : ∀ g v, q g v = ‖(g : StrongDual ℂ E) v‖ := fun _ _ => rfl
  have hqc : ∀ g, Continuous (q g) := by
    intro g
    have : (q g : E → ℝ) = fun v => ‖(g : StrongDual ℂ E) v‖ := funext (hq g)
    rw [this]
    exact continuous_norm.comp (g : StrongDual ℂ E).continuous
  have hbdd : BddAbove (Set.range q) := by
    rw [Seminorm.bddAbove_range_iff]
    intro v
    have hN : {g : StrongDual ℂ E | ∀ y ∈ ({v} : Set E), g y ∈ Metric.closedBall (0 : ℂ) 1}
        ∈ 𝓝 (0 : StrongDual ℂ E) :=
      (ContinuousLinearMap.hasBasis_nhds_zero).mem_of_mem
        (i := (({v} : Set E), Metric.closedBall (0 : ℂ) 1))
        ⟨isVonNBounded_singleton v, Metric.closedBall_mem_nhds _ one_pos⟩
    obtain ⟨a, ha⟩ := (hC hN).eventually.exists
    refine ⟨‖a‖, ?_⟩
    rintro _ ⟨g, rfl⟩
    obtain ⟨h, hh, hgh⟩ := ha g.2
    have h1 := hh v rfl
    rw [mem_closedBall_zero_iff] at h1
    show q g v ≤ ‖a‖
    rw [hq, ← hgh, ContinuousLinearMap.smul_apply, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg a) h1
  refine ⟨⨆ g, q g, ?_, fun g hg v => ?_⟩
  · rw [Seminorm.coe_iSup_eq hbdd]
    exact Seminorm.continuous_iSup q hqc hbdd
  · have hle : q ⟨g, hg⟩ ≤ ⨆ g, q g := le_ciSup hbdd ⟨g, hg⟩
    exact (hq ⟨g, hg⟩ v).symm.le.trans (hle v)

end barrel

section srefl

open MasulloGRH Bornology

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E]
variable {κE : Type*} {pE : SeminormFamily ℂ E κE} (hE : WithSeminorms pE)
variable {ι : Type*} (φ : ι → StrongDual ℂ E) (e : ι → E) (c : ι → ℝ)
variable (hexp : ∀ x, HasSum (fun j => φ j x • e j) x)
variable (hc0 : ∀ j, 0 < c j) (hcs : Summable c)
variable (hdom : ∀ P : Seminorm ℂ E, Continuous P → ∃ P' : Seminorm ℂ E, Continuous P' ∧
  ∀ j x, P (e j) * ‖φ j x‖ ≤ c j * P' x)

lemma ext_of_dual [T2Space E] (hE : WithSeminorms pE) {x y : E}
    (h : ∀ T : StrongDual ℂ E, T x = T y) : x = y := by
  by_contra hne
  have hd : x - y ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨i, hi⟩ := hE.separating_of_T1 (x - y) hd
  obtain ⟨g, -, hg⟩ := hb_norm hE (pE i) (hE.continuous_seminorm i) (x - y)
  rw [map_sub, h g, sub_self, norm_zero] at hg
  exact hi hg.symm

include hE hexp hc0 hcs hdom in
theorem srefl [CompleteSpace E] [T2Space E] (Ψ : StrongDual ℂ (StrongDual ℂ E)) :
    ∃! x : E, ∀ T : StrongDual ℂ E, Ψ T = T x := by
  classical
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (dws (E := E))
    ((normSeminorm ℂ ℂ).comp (Ψ : StrongDual ℂ E →ₗ[ℂ] ℂ)) (continuous_norm.comp Ψ.continuous)
  let Bs := bU s
  have hΨ : ∀ T, ‖Ψ T‖ ≤ C * dsn Bs T := fun T => by
    have := hC T
    rw [smul_apply, NNReal.smul_def, smul_eq_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_left (sup_dsn_le s T) C.2)
  have hsm : Summable fun j => Ψ (φ j) • e j := by
    refine summable_of_sn hE _ fun i => ?_
    obtain ⟨P', hP', hdP⟩ := hdom (pE i) (hE.continuous_seminorm i)
    obtain ⟨M, hM⟩ := bdd_of_cont hP' Bs.2
    have hb : ∀ j, pE i (e j) * dsn Bs (φ j) ≤ c j * max M 0 := by
      intro j
      have h1 : dsn Bs (((pE i (e j) : ℝ) : ℂ) • φ j) ≤ c j * max M 0 :=
        dsn_le Bs _ (mul_nonneg (hc0 j).le (le_max_right _ _)) fun x hx => by
          rw [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
          exact (hdP j x).trans (mul_le_mul_of_nonneg_left ((hM x hx).trans (le_max_left _ _))
            (hc0 j).le)
      rwa [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (apply_nonneg _ _)] at h1
    refine Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) (fun j => ?_)
      ((hcs.mul_right (max M 0)).mul_left (C : ℝ))
    rw [map_smul_eq_mul]
    calc ‖Ψ (φ j)‖ * pE i (e j) ≤ C * dsn Bs (φ j) * pE i (e j) :=
          mul_le_mul_of_nonneg_right (hΨ _) (apply_nonneg _ _)
      _ = C * (pE i (e j) * dsn Bs (φ j)) := by ring
      _ ≤ C * (c j * max M 0) := mul_le_mul_of_nonneg_left (hb j) C.2
  obtain ⟨x, hx⟩ := hsm
  have key : ∀ T : StrongDual ℂ E, Ψ T = T x := by
    intro T
    have h1 : HasSum (fun j => Ψ (φ j) * T (e j)) (T x) := by
      have := T.hasSum hx
      simpa [map_smul, smul_eq_mul] using this
    have h2 : HasSum (fun j => Ψ (φ j) * T (e j)) (Ψ T) := by
      have := Ψ.hasSum (dexp hE φ e c hexp hc0 hcs hdom T)
      simp only [map_smul, smul_eq_mul] at this
      exact this.congr_fun fun j => mul_comm _ _
    exact h2.unique h1
  exact ⟨x, key, fun y hy => ext_of_dual hE fun T => by rw [← hy T, key T]⟩

end srefl

section sbtop

open MasulloGRH Bornology
open scoped UniformConvergence

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
variable {κE : Type*} {pE : SeminormFamily ℂ E κE} (hE : WithSeminorms pE)

/-- the unit ball of the dual for a seminorm -/
def polar (P : Seminorm ℂ E) : Set (StrongDual ℂ E) := {g | ∀ z, ‖g z‖ ≤ P z}

omit [BarrelledSpace ℂ E] in
lemma polar_bdd (P : Seminorm ℂ E) (hP : Continuous P) : IsVonNBounded ℂ (polar P) :=
  dual_bdd_of fun B => by
    obtain ⟨M, hM⟩ := bdd_of_cont hP B.2
    exact ⟨M, fun g hg x hx => (hg x).trans (hM x hx)⟩

include hE in
theorem sbE : ‹TopologicalSpace E› = strongBidualTopology E := by
  let 𝔅 : Set (Set (StrongDual ℂ E)) := {B | IsVonNBounded ℂ B}
  let Ψ : E → (StrongDual ℂ E →ᵤ[𝔅] ℂ) := fun x => UniformOnFun.ofFun 𝔅 (fun f => f x)
  have hsb : strongBidualTopology E = TopologicalSpace.induced Ψ inferInstance := rfl
  apply le_antisymm
  · rw [hsb, ← continuous_iff_le_induced, continuous_iff_continuousAt]
    intro x0
    rw [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
    intro B hB
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨P, hP, hPB⟩ := barrel_bound (E := E) hB
    have hev : ∀ᶠ x in 𝓝 x0, P (x - x0) < ε := by
      have h : Tendsto (fun x => P (x - x0)) (𝓝 x0) (𝓝 (P (x0 - x0))) :=
        (hP.comp (continuous_sub_right x0)).tendsto x0
      rw [sub_self, map_zero] at h
      exact h.eventually (Iio_mem_nhds hε)
    filter_upwards [hev] with x hx f hf
    show dist (f x0) (f x) < ε
    rw [dist_eq_norm, ← map_sub]
    refine lt_of_le_of_lt (hPB f hf _) ?_
    rwa [map_sub_rev]
  · refine (@continuous_id_iff_le E (strongBidualTopology E) _).1 ?_
    rw [@continuous_iff_continuousAt E E (strongBidualTopology E) _]
    intro x0
    show Tendsto id (@nhds E (strongBidualTopology E) x0) (𝓝 x0)
    rw [hE.tendsto_nhds id x0]
    intro i ε hε
    have hT : Tendsto Ψ (@nhds E (strongBidualTopology E) x0) (𝓝 (Ψ x0)) := by
      rw [hsb, nhds_induced]
      exact tendsto_comap
    rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at hT
    have hev := Metric.tendstoUniformlyOn_iff.1
      (hT (polar (pE i)) (polar_bdd (pE i) (hE.continuous_seminorm i))) (ε / 2) (half_pos hε)
    filter_upwards [hev] with x hx
    obtain ⟨g, hg, hgx⟩ := hb_norm hE (pE i) (hE.continuous_seminorm i) (x - x0)
    have := hx g hg
    change dist (g x0) (g x) < ε / 2 at this
    rw [dist_eq_norm, ← map_sub, ← norm_neg, ← map_neg, neg_sub, hgx] at this
    show pE i (x - x0) < ε
    linarith

end sbtop

section drefl

open MasulloGRH Bornology
open scoped UniformConvergence

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
variable {κE : Type*} {pE : SeminormFamily ℂ E κE} (hE : WithSeminorms pE)

/-- evaluation as a continuous linear map into the strong bidual -/
def evlC : E →L[ℂ] StrongDual ℂ (StrongDual ℂ E) where
  toFun := evl
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := by
    let _ : ContinuousAdd (StrongDual ℂ (StrongDual ℂ E)) :=
      (inferInstance : IsTopologicalAddGroup (StrongDual ℂ (StrongDual ℂ E))).toContinuousAdd
    refine continuous_of_continuousAt_zero
      ({ toFun := evl, map_add' := fun _ _ => by ext; simp,
         map_smul' := fun _ _ => by ext; simp } : E →ₗ[ℂ] StrongDual ℂ (StrongDual ℂ E)) ?_
    rw [ContinuousAt, LinearMap.map_zero]
    refine (ContinuousLinearMap.hasBasis_nhds_zero).tendsto_right_iff.2 ?_
    rintro ⟨𝔄, U⟩ ⟨h𝔄, hU⟩
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨P, hP, hPB⟩ := barrel_bound (E := E) h𝔄
    have h0 := hP.tendsto 0
    rw [map_zero] at h0
    filter_upwards [h0.eventually (Iio_mem_nhds hε)] with x hx g hg
    apply hεU
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (hPB g hg x) hx

include hE in
theorem drefl [T2Space E]
    (hsr : ∀ Ψ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ T : StrongDual ℂ E, Ψ T = T x) :
    IsReflexive (StrongDual ℂ E) := by
  have hG : ∀ G : StrongDual ℂ (StrongDual ℂ E), ∃ x : E, G = evl x := fun G => by
    obtain ⟨x, hx, -⟩ := hsr G
    exact ⟨x, ContinuousLinearMap.ext fun T => hx T⟩
  refine ⟨fun Φ => ?_, ?_⟩
  · let T : StrongDual ℂ E := Φ.comp evlC
    refine ⟨T, fun G => ?_, fun T' hT' => ?_⟩
    · obtain ⟨x, rfl⟩ := hG G
      rfl
    · refine ContinuousLinearMap.ext fun x => ?_
      have := hT' (evl x)
      rw [evl_apply] at this
      rw [← this]
      rfl
  · let 𝔅 : Set (Set (StrongDual ℂ (StrongDual ℂ E))) := {B | IsVonNBounded ℂ B}
    let Ψ : StrongDual ℂ E → (StrongDual ℂ (StrongDual ℂ E) →ᵤ[𝔅] ℂ) :=
      fun T => UniformOnFun.ofFun 𝔅 (fun G => G T)
    have hsb : strongBidualTopology (StrongDual ℂ E) = TopologicalSpace.induced Ψ inferInstance := rfl
    apply le_antisymm
    · rw [hsb, ← continuous_iff_le_induced, continuous_iff_continuousAt]
      intro T0
      rw [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
      intro 𝔊 h𝔊
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      let B : Set E := {x | evl x ∈ 𝔊}
      have hB : IsVonNBounded ℂ B := by
        rw [hE.isVonNBounded_iff_seminorm_bounded]
        intro i
        let A : BI (StrongDual ℂ E) := ⟨polar (pE i), polar_bdd (pE i) (hE.continuous_seminorm i)⟩
        obtain ⟨R, hR⟩ := bdd_of_cont (dsn_cont A) (h𝔊 : IsVonNBounded ℂ 𝔊)
        refine ⟨max R 0 + 1, by positivity, fun x hx => lt_of_le_of_lt ?_ (lt_add_one _)⟩
        obtain ⟨g, hg, hgx⟩ := hb_norm hE (pE i) (hE.continuous_seminorm i) x
        rw [← hgx]
        exact (le_dsn A (evl x) (x := g) hg).trans ((hR _ hx).trans (le_max_left _ _))
      have hev : ∀ᶠ T in 𝓝 T0, dsn (⟨B, hB⟩ : BI E) (T - T0) < ε := by
        have h : Tendsto (fun T => dsn (⟨B, hB⟩ : BI E) (T - T0)) (𝓝 T0)
            (𝓝 (dsn (⟨B, hB⟩ : BI E) (T0 - T0))) :=
          ((dsn_cont _).comp (continuous_sub_right T0)).tendsto T0
        rw [sub_self, map_zero] at h
        exact h.eventually (Iio_mem_nhds hε)
      filter_upwards [hev] with T hT G hG'
      obtain ⟨x, rfl⟩ := hG G
      show dist (T0 x) (T x) < ε
      rw [dist_eq_norm, norm_sub_rev]
      refine lt_of_le_of_lt ?_ hT
      have := le_dsn (⟨B, hB⟩ : BI E) (T - T0) (x := x) hG'
      simpa using this
    · refine (@continuous_id_iff_le _ (strongBidualTopology (StrongDual ℂ E)) _).1 ?_
      rw [@continuous_iff_continuousAt _ _ (strongBidualTopology (StrongDual ℂ E)) _]
      intro T0
      show Tendsto id (@nhds _ (strongBidualTopology (StrongDual ℂ E)) T0) (𝓝 T0)
      rw [(dws (E := E)).tendsto_nhds id T0]
      intro B ε hε
      have hT : Tendsto Ψ (@nhds _ (strongBidualTopology (StrongDual ℂ E)) T0) (𝓝 (Ψ T0)) := by
        rw [hsb, nhds_induced]
        exact tendsto_comap
      rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at hT
      have h𝔊 : IsVonNBounded ℂ (evl '' B.1 : Set (StrongDual ℂ (StrongDual ℂ E))) := by
        refine dual_bdd_of fun A => ?_
        obtain ⟨P, hP, hPA⟩ := barrel_bound (E := E) A.2
        obtain ⟨M, hM⟩ := bdd_of_cont hP B.2
        refine ⟨M, ?_⟩
        rintro _ ⟨x, hx, rfl⟩ g hg
        exact (hPA g hg x).trans (hM x hx)
      have hev := Metric.tendstoUniformlyOn_iff.1 (hT _ h𝔊) (ε / 2) (half_pos hε)
      filter_upwards [hev] with T hT'
      show dsn B (T - T0) < ε
      refine lt_of_le_of_lt (dsn_le B _ (by positivity) fun x hx => ?_) (half_lt_self hε)
      have := hT' (evl x) ⟨x, hx, rfl⟩
      change dist (T0 x) (T x) < ε / 2 at this
      rw [dist_eq_norm, norm_sub_rev] at this
      rw [ContinuousLinearMap.sub_apply]
      exact this.le

end drefl

section dmontel

open MasulloGRH Bornology

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
variable {κE : Type*} {pE : SeminormFamily ℂ E κE} (hE : WithSeminorms pE)
variable {ι : Type*} (φ : ι → StrongDual ℂ E) (e : ι → E) (c : ι → ℝ)
variable (hexp : ∀ x, HasSum (fun j => φ j x • e j) x)
variable (hc0 : ∀ j, 0 < c j) (hcs : Summable c)
variable (hdom : ∀ P : Seminorm ℂ E, Continuous P → ∃ P' : Seminorm ℂ E, Continuous P' ∧
  ∀ j x, P (e j) * ‖φ j x‖ ≤ c j * P' x)

lemma sn_hasSum_le {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] {P : Seminorm ℂ V}
    (hP : Continuous P) {ι : Type*} {f : ι → V} {s : V} (hf : HasSum f s)
    (hs : Summable fun j => P (f j)) : P s ≤ ∑' j, P (f j) := by
  refine le_of_tendsto ((hP.tendsto s).comp hf) (Eventually.of_forall fun J => ?_)
  exact (Finset.le_sum_of_subadditive (⇑P) (map_zero _).le (map_add_le_add _) J f).trans
    (hs.sum_le_tsum J fun j _ => apply_nonneg _ _)

include hE hexp hc0 hcs hdom in
theorem dual_compact [CompleteSpace (StrongDual ℂ E)] [T2Space (StrongDual ℂ E)]
    (A : Set (StrongDual ℂ E)) (hAc : IsClosed A) (hAb : IsVonNBounded ℂ A) : IsCompact A := by
  classical
  obtain ⟨P, hP, hPA⟩ := barrel_bound (E := E) hAb
  obtain ⟨P', hP', hdP⟩ := hdom P hP
  let K : Set (ι → ℂ) := Set.univ.pi fun j => Metric.closedBall (0 : ℂ) (P (e j))
  have hK : IsCompact K := isCompact_univ_pi fun j => isCompact_closedBall _ _
  -- bounds on the frame functionals
  have hβ : ∀ B : BI E, ∃ M, 0 ≤ M ∧ ∀ j, P (e j) * dsn B (φ j) ≤ c j * M := by
    intro B
    obtain ⟨M, hM⟩ := bdd_of_cont hP' B.2
    refine ⟨max M 0, le_max_right _ _, fun j => ?_⟩
    have h1 : dsn B (((P (e j) : ℝ) : ℂ) • φ j) ≤ c j * max M 0 :=
      dsn_le B _ (mul_nonneg (hc0 j).le (le_max_right _ _)) fun x hx => by
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
        exact (hdP j x).trans (mul_le_mul_of_nonneg_left ((hM x hx).trans (le_max_left _ _))
          (hc0 j).le)
    rwa [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (apply_nonneg _ _)] at h1
  have hsumm : ∀ a ∈ K, ∀ B : BI E, Summable fun j => dsn B (a j • φ j) := by
    intro a ha B
    obtain ⟨M, -, hM⟩ := hβ B
    refine Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) (fun j => ?_) (hcs.mul_right M)
    rw [map_smul_eq_mul]
    have haj : ‖a j‖ ≤ P (e j) := mem_closedBall_zero_iff.1 (ha j (Set.mem_univ j))
    exact (mul_le_mul_of_nonneg_right haj (apply_nonneg _ _)).trans (hM j)
  let R : (ι → ℂ) → StrongDual ℂ E := fun a => ∑' j, a j • φ j
  have hR : ∀ a ∈ K, HasSum (fun j => a j • φ j) (R a) := fun a ha =>
    (summable_of_sn (dws (E := E)) _ (hsumm a ha)).hasSum
  have hsub : A ⊆ R '' K := by
    intro T hT
    refine ⟨fun j => T (e j), fun j _ => mem_closedBall_zero_iff.2 (hPA T hT (e j)), ?_⟩
    exact (dexp hE φ e c hexp hc0 hcs hdom T).tsum_eq
  have hcont : ContinuousOn R K := by
    intro a0 ha0
    show Tendsto R (𝓝[K] a0) (𝓝 (R a0))
    rw [(dws (E := E)).tendsto_nhds R (R a0)]
    intro B ε hε
    obtain ⟨M, hM0, hM⟩ := hβ B
    have hMc : Tendsto (fun J : Finset ι => ∑' j : ↥((J : Set ι)ᶜ), c j) atTop (𝓝 0) :=
      tendsto_tsum_compl_atTop_zero c
    obtain ⟨J, hJ⟩ := (hMc.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / (4 * (M + 1)) by
      positivity))).exists
    let S := ∑ j ∈ J, dsn B (φ j)
    let δ := ε / (4 * (S + 1))
    have hδ : 0 < δ := by positivity
    have hN : {a : ι → ℂ | ∀ j ∈ J, a j ∈ Metric.ball (a0 j) δ} ∈ 𝓝 a0 := by
      have := set_pi_mem_nhds (s := fun j => Metric.ball (a0 j) δ) J.finite_toSet
        (fun j _ => Metric.ball_mem_nhds _ hδ)
      refine Filter.mem_of_superset this fun a ha j hj => ha j hj
    filter_upwards [inter_mem_nhdsWithin K hN, self_mem_nhdsWithin] with a ha haK
    have hdiff : HasSum (fun j => (a j - a0 j) • φ j) (R a - R a0) := by
      have := (hR a haK).sub (hR a0 ha0)
      convert this using 1
      all_goals first | rfl | (funext j; exact sub_smul (a j) (a0 j) (φ j))
    have hb : ∀ j, dsn B ((a j - a0 j) • φ j) ≤ 2 * (c j * M) := by
      intro j
      rw [map_smul_eq_mul]
      have h1 : ‖a j - a0 j‖ ≤ 2 * P (e j) := by
        have h2 := mem_closedBall_zero_iff.1 (haK j (Set.mem_univ j))
        have h3 := mem_closedBall_zero_iff.1 (ha0 j (Set.mem_univ j))
        linarith [norm_sub_le (a j) (a0 j)]
      calc ‖a j - a0 j‖ * dsn B (φ j) ≤ 2 * P (e j) * dsn B (φ j) :=
            mul_le_mul_of_nonneg_right h1 (apply_nonneg _ _)
        _ = 2 * (P (e j) * dsn B (φ j)) := by ring
        _ ≤ 2 * (c j * M) := mul_le_mul_of_nonneg_left (hM j) (by norm_num)
    have hs2 : Summable fun j => dsn B ((a j - a0 j) • φ j) :=
      Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) hb ((hcs.mul_right M).mul_left 2)
    refine lt_of_le_of_lt (sn_hasSum_le (dsn_cont B) hdiff hs2) ?_
    rw [← hs2.sum_add_tsum_compl (s := J)]
    have h1 : ∑ j ∈ J, dsn B ((a j - a0 j) • φ j) ≤ δ * S := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [map_smul_eq_mul]
      have := ha.2 j hj
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact mul_le_mul_of_nonneg_right this.le (apply_nonneg _ _)
    have h2 : ∑' j : ↥((J : Set ι)ᶜ), dsn B ((a j - a0 j) • φ j) ≤
        ∑' j : ↥((J : Set ι)ᶜ), 2 * (c j * M) :=
      (hs2.subtype _).tsum_le_tsum (fun j => hb j) (((hcs.subtype _).mul_right M).mul_left 2)
    have h3 : ∑' j : ↥((J : Set ι)ᶜ), 2 * (c j * M) = 2 * M * ∑' j : ↥((J : Set ι)ᶜ), c j := by
      rw [← tsum_mul_left]; congr 1; funext j; ring
    have h4 : δ * S < ε / 2 := by
      show ε / (4 * (S + 1)) * S < ε / 2
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => apply_nonneg _ _
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h5 : 2 * M * ∑' j : ↥((J : Set ι)ᶜ), c j ≤ ε / 2 := by
      have hc' : 0 ≤ ∑' j : ↥((J : Set ι)ᶜ), c j := tsum_nonneg fun j => (hc0 j).le
      have := hJ.le
      calc 2 * M * ∑' j : ↥((J : Set ι)ᶜ), c j ≤ 2 * M * (ε / (4 * (M + 1))) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ ε / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    linarith
  exact (hK.image_of_continuousOn hcont).of_isClosed_subset hAc hsub

end dmontel

/-! ### assembly for the Schwartz space -/

section asm

open MasulloGRH Bornology

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

variable (m : ℕ)

instance sch_ucg : (uniformity (Sch m)).IsCountablyGenerated :=
  IsUniformAddGroup.uniformity_countably_generated

lemma sch_hlcs_ws : WithSeminorms (schwartzSeminormFamily ℂ (V m) ℂ) := schwartz_withSeminorms ℂ (V m) ℂ

end asm

end

end Aux_SEN


set_option autoImplicit false

namespace Aux_ESF

open MasulloGRH Topology Filter Set

noncomputable section

variable {m n r s : ℕ} {d : Fin s → ℕ}

abbrev XT (m n : ℕ) := (Fin m → ℝ) × (Fin n → ℝ)
abbrev QQ (m n r s : ℕ) (d : Fin s → ℕ) :=
  (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ))
abbrev ES (m n r s : ℕ) (d : Fin s → ℕ) := ElemSchwartz m n r s d

lemma rd_zero : IsRapidDecay (0 : ElemGroup m n r s d → ℂ) := by
  have h0 : ∀ a b, elemLift (0 : ElemGroup m n r s d → ℂ) a b = 0 := fun _ _ => rfl
  refine ⟨fun a b => by rw [h0]; exact contDiff_const, fun i j k => ⟨0, fun a b xt => ?_⟩⟩
  rw [h0]
  simp

lemma rd_add {f g : ElemGroup m n r s d → ℂ} (hf : IsRapidDecay f) (hg : IsRapidDecay g) :
    IsRapidDecay (f + g) := by
  have h0 : ∀ a b, elemLift (f + g) a b = elemLift f a b + elemLift g a b := fun _ _ => rfl
  refine ⟨fun a b => by rw [h0]; exact (hf.1 a b).add (hg.1 a b), fun i j k => ?_⟩
  obtain ⟨C1, h1⟩ := hf.2 i j k
  obtain ⟨C2, h2⟩ := hg.2 i j k
  refine ⟨C1 + C2, fun a b xt => ?_⟩
  rw [h0, iteratedFDeriv_add_apply ((hf.1 a b).contDiffAt.of_le (by exact_mod_cast le_top))
    ((hg.1 a b).contDiffAt.of_le (by exact_mod_cast le_top))]
  have := norm_add_le (iteratedFDeriv ℝ k (elemLift f a b) xt) (iteratedFDeriv ℝ k (elemLift g a b) xt)
  have hp : 0 ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i := by positivity
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt + iteratedFDeriv ℝ k (elemLift g a b) xt‖
      ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖iteratedFDeriv ℝ k (elemLift f a b) xt‖ + ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖) :=
        mul_le_mul_of_nonneg_left this hp
    _ = ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖ +
        ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖ := by ring
    _ ≤ C1 + C2 := add_le_add (h1 a b xt) (h2 a b xt)

lemma rd_smul (c : ℂ) {f : ElemGroup m n r s d → ℂ} (hf : IsRapidDecay f) :
    IsRapidDecay (c • f) := by
  have h0 : ∀ a b, elemLift (c • f) a b = c • elemLift f a b := fun _ _ => rfl
  refine ⟨fun a b => by rw [h0]; exact (hf.1 a b).const_smul c, fun i j k => ?_⟩
  obtain ⟨C1, h1⟩ := hf.2 i j k
  refine ⟨‖c‖ * C1, fun a b xt => ?_⟩
  rw [h0, iteratedFDeriv_const_smul_apply ((hf.1 a b).contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul]
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖c‖ * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖)
      = ‖c‖ * (‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖) := by ring
    _ ≤ ‖c‖ * C1 := mul_le_mul_of_nonneg_left (h1 a b xt) (norm_nonneg c)

lemma rd (g : ES m n r s d) : IsRapidDecay g.toFun := by
  have h := g.2
  change g.1 ∈ Submodule.span ℂ {g | IsRapidDecay g} at h
  show IsRapidDecay g.1
  exact Submodule.span_induction (p := fun x _ => IsRapidDecay x) (fun x hx => hx) rd_zero
    (fun x y _ _ hx hy => rd_add hx hy) (fun c x _ hx => rd_smul c hx) h

lemma lift_smooth (g : ES m n r s d) (a b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (elemLift g.toFun a b) := (rd g).1 a b

lemma lift_add (f g : ES m n r s d) (a b) :
    elemLift (f + g).toFun a b = elemLift f.toFun a b + elemLift g.toFun a b := rfl

lemma lift_smul (c : ℂ) (g : ES m n r s d) (a b) :
    elemLift (c • g).toFun a b = c • elemLift g.toFun a b := rfl

/-- the weighted derivative (as in the topology instance) -/
def wtd (p : ℕ × ℕ × ℕ) (q : QQ m n r s d) :
    ES m n r s d →ₗ[ℂ] ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => XT m n) ℂ where
  toFun g := (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
    iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2
  map_add' f g := by
    rw [lift_add, iteratedFDeriv_add_apply ((lift_smooth f _ _).contDiffAt.of_le
      (by exact_mod_cast le_top)) ((lift_smooth g _ _).contDiffAt.of_le (by exact_mod_cast le_top)),
      smul_add]
  map_smul' c g := by
    simp only [RingHom.id_apply]
    rw [lift_smul, iteratedFDeriv_const_smul_apply ((lift_smooth g _ _).contDiffAt.of_le
      (by exact_mod_cast le_top)), smul_comm]

lemma norm_wtd (p : ℕ × ℕ × ℕ) (q : QQ m n r s d) (g : ES m n r s d) :
    ‖wtd p q g‖ = ‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1 *
      ‖iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2‖ := by
  simp only [wtd, LinearMap.coe_mk, AddHom.coe_mk]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

def snq (p : ℕ × ℕ × ℕ) (q : QQ m n r s d) : Seminorm ℂ (ES m n r s d) :=
  (normSeminorm ℂ _).comp (wtd p q)

lemma snq_apply (p : ℕ × ℕ × ℕ) (q : QQ m n r s d) (g : ES m n r s d) :
    snq p q g = ‖wtd p q g‖ := rfl

lemma snq_bdd (p : ℕ × ℕ × ℕ) : BddAbove (range (snq (m := m) (n := n) (r := r) (d := d) p)) := by
  rw [Seminorm.bddAbove_range_iff]
  intro g
  obtain ⟨C, hC⟩ := (rd g).2 p.1 p.2.1 p.2.2
  exact ⟨C, by rintro _ ⟨q, rfl⟩; show snq p q g ≤ C; rw [snq_apply, norm_wtd]; exact hC _ _ _⟩

/-- the seminorms of `S(ℝ^m × 𝕋^n × ℤ^r × F)` -/
def sn (p : ℕ × ℕ × ℕ) : Seminorm ℂ (ES m n r s d) := ⨆ q, snq p q

lemma sn_apply (p : ℕ × ℕ × ℕ) (g : ES m n r s d) : sn p g = ⨆ q, ‖wtd p q g‖ := by
  rw [sn, Seminorm.coe_iSup_eq (snq_bdd p), iSup_apply]; rfl

lemma le_sn (p : ℕ × ℕ × ℕ) (g : ES m n r s d) (q : QQ m n r s d) :
    ‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1 *
      ‖iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2‖ ≤ sn p g := by
  rw [← norm_wtd, sn_apply]
  obtain ⟨C, hC⟩ := (rd g).2 p.1 p.2.1 p.2.2
  refine le_ciSup (f := fun q => ‖wtd p q g‖) ⟨C, ?_⟩ q
  rintro _ ⟨q, rfl⟩; show ‖wtd p q g‖ ≤ C; rw [norm_wtd]; exact hC _ _ _

lemma sn_le (p : ℕ × ℕ × ℕ) (g : ES m n r s d) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a b xt, ‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 *
      ‖iteratedFDeriv ℝ p.2.2 (elemLift g.toFun a b) xt‖ ≤ M) : sn p g ≤ M := by
  rw [sn_apply]
  refine ciSup_le fun q => ?_
  rw [norm_wtd]; exact h _ _ _

/-- the map defining the topology -/
def Φ : ES m n r s d →+ ((p : ℕ × ℕ × ℕ) →
    UniformFun (QQ m n r s d) (ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => XT m n) ℂ)) where
  toFun g p := UniformFun.ofFun (fun q => wtd p q g)
  map_zero' := by funext p; simp only [map_zero]; rfl
  map_add' f g := by funext p; simp only [map_add]; rfl

lemma top_eq : (inferInstance : TopologicalSpace (ES m n r s d)) =
    TopologicalSpace.induced (Φ (m := m) (n := n) (r := r) (d := d)) inferInstance := rfl

instance esTG : IsTopologicalAddGroup (ES m n r s d) :=
  topologicalAddGroup_induced (Φ (m := m) (n := n) (r := r) (d := d))

lemma comap_eq (p : ℕ × ℕ × ℕ) :
    (𝓝 (0 : UniformFun (QQ m n r s d) (ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => XT m n) ℂ))).comap
      (fun g : ES m n r s d => Φ g p) = (𝓝 0).comap (sn (m := m) (n := n) (r := r) (d := d) p) := by
  have hb := (UniformFun.hasBasis_nhds_zero_of_basis (α := QQ m n r s d)
    (Metric.nhds_basis_ball (x := (0 : ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => XT m n) ℂ)))).comap
    (fun g : ES m n r s d => Φ g p)
  have hb2 := (Metric.nhds_basis_ball (x := (0 : ℝ))).comap (sn (m := m) (n := n) (r := r) (d := d) p)
  refine le_antisymm ?_ ?_
  · rw [hb.le_basis_iff hb2]
    intro ε hε
    refine ⟨ε / 2, half_pos hε, fun g hg => ?_⟩
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (apply_nonneg _ _)]
    have : sn p g ≤ ε / 2 := by
      rw [sn_apply]
      refine ciSup_le fun q => ?_
      have := hg q
      simp only [Metric.mem_ball, dist_zero_right] at this
      exact this.le
    linarith
  · rw [hb2.le_basis_iff hb]
    intro ε hε
    refine ⟨ε, hε, fun g hg q => ?_⟩
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (apply_nonneg _ _)] at hg
    simp only [Metric.mem_ball, dist_zero_right]
    show ‖wtd p q g‖ < ε
    refine lt_of_le_of_lt ?_ hg
    rw [norm_wtd]; exact le_sn p g q

theorem es_ws : WithSeminorms (sn (m := m) (n := n) (r := r) (d := d)) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  have h0 : 𝓝 (0 : ES m n r s d) = comap (Φ (m := m) (n := n) (r := r) (d := d)) (𝓝 0) := by
    have h := @nhds_induced _ _ _ (Φ (m := m) (n := n) (r := r) (d := d)) 0
    rw [map_zero] at h
    exact h
  rw [h0, nhds_pi, Filter.pi, Filter.comap_iInf]
  refine iInf_congr fun p => ?_
  rw [Filter.comap_comap]
  exact comap_eq p

end

end Aux_ESF


namespace Aux_ESF

open MasulloGRH Topology Filter Set Aux_SEN

noncomputable section

/-! ### general helpers -/

section gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cs_boundG {g : E → ℂ} (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hc : HasCompactSupport g)
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

lemma leibG {a g : E → ℂ} (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : E) {d : ℕ} {M B : ℝ}
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

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

lemma norm_comp_clm_le {f : E' → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (L : E →L[ℝ] E')
    (hL : ‖L‖ ≤ 1) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ i f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _j : Fin i, ‖L‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => hL
  calc ‖iteratedFDeriv ℝ i f (L x)‖ * ∏ _j : Fin i, ‖L‖ ≤ ‖iteratedFDeriv ℝ i f (L x)‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

lemma pow3_le (p q t : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : 0 ≤ t) (M : ℕ) :
    (p + q + t) ^ M ≤ 3 ^ M * (p ^ M + q ^ M + t ^ M) := by
  set μ := max p (max q t)
  have h1 : p + q + t ≤ 3 * μ := by
    have := le_max_left p (max q t); have := le_max_right p (max q t)
    have := le_max_left q t; have := le_max_right q t; linarith
  have h2 : μ ^ M ≤ p ^ M + q ^ M + t ^ M := by
    rcases le_total q t with hqt | hqt
    · rcases le_total p t with hpt | hpt
      · have : μ = t := by simp [μ, max_eq_right hqt, max_eq_right hpt]
        rw [this]; have := pow_nonneg hp M; have := pow_nonneg hq M; linarith
      · have : μ = p := by simp [μ, max_eq_right hqt, max_eq_left hpt]
        rw [this]; have := pow_nonneg ht M; have := pow_nonneg hq M; linarith
    · rcases le_total p q with hpq | hpq
      · have : μ = q := by simp [μ, max_eq_left hqt, max_eq_right hpq]
        rw [this]; have := pow_nonneg hp M; have := pow_nonneg ht M; linarith
      · have : μ = p := by simp [μ, max_eq_left hqt, max_eq_left hpq]
        rw [this]; have := pow_nonneg ht M; have := pow_nonneg hq M; linarith
  calc (p + q + t) ^ M ≤ (3 * μ) ^ M := pow_le_pow_left₀ (by positivity) h1 M
    _ = 3 ^ M * μ ^ M := mul_pow _ _ _
    _ ≤ 3 ^ M * (p ^ M + q ^ M + t ^ M) := mul_le_mul_of_nonneg_left h2 (by positivity)

end gen

/-! ### cutoffs -/

def th1 (t : ℝ) : ℝ := psi (t / 2)
def ro1 (t : ℝ) : ℝ := rho (t / 2)
def be1 (u : ℝ) : ℝ := rho (4 * u)

lemma th1_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) th1 :=
  psi_smooth.comp (contDiff_id.div_const 2)
lemma ro1_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ro1 :=
  rho_smooth.comp (contDiff_id.div_const 2)
lemma be1_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) be1 :=
  rho_smooth.comp (contDiff_const.mul contDiff_id)

lemma th1_supp {t : ℝ} (h : th1 t ≠ 0) : |t| < 3 / 4 := by
  by_contra h'
  exact h (psi_zero (by rw [abs_div, abs_two]; linarith))

lemma ro1_one {t : ℝ} (h : |t| < 3 / 4) : ro1 t = 1 :=
  rho_one (by rw [abs_div, abs_two]; linarith)

lemma ro1_supp {t : ℝ} (h : ro1 t ≠ 0) : |t| < 7 / 8 := by
  by_contra h'
  exact h (rho_zero (by rw [abs_div, abs_two]; linarith))

lemma be1_supp {u : ℝ} (h : be1 u ≠ 0) : |u| < 7 / 64 := by
  by_contra h'
  exact h (rho_zero (by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith))

lemma be1_zero : be1 0 = 1 := rho_one (by norm_num)

variable {m n r s : ℕ} {d : Fin s → ℕ}

def kR (k : Fin n → ℤ) : Fin n → ℝ := fun i => (k i : ℝ)

/-- the partition of unity on `ℝ^n` along `ℤ^n` -/
def Th (t : Fin n → ℝ) : ℝ := ∏ i, th1 (t i)
/-- the plateau on `ℝ^n` -/
def P0 (t : Fin n → ℝ) : ℝ := ∏ i, ro1 (t i)

lemma coordR_smooth {k : ℕ} (i : Fin k) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin k → ℝ => x i) :=
  contDiff_apply ℝ ℝ i

lemma Th_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Th (n := n)) :=
  contDiff_prod fun i _ => th1_smooth.comp (coordR_smooth i)

lemma P0_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P0 (n := n)) :=
  contDiff_prod fun i _ => ro1_smooth.comp (coordR_smooth i)

lemma Th_supp {t : Fin n → ℝ} (h : Th t ≠ 0) (i : Fin n) : |t i| < 3 / 4 :=
  th1_supp (Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i))

lemma P0_supp {t : Fin n → ℝ} (h : P0 t ≠ 0) (i : Fin n) : |t i| < 7 / 8 :=
  ro1_supp (Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i))

lemma P0_Th (t : Fin n → ℝ) : P0 t * Th t = Th t := by
  by_cases h : Th t = 0
  · rw [h, mul_zero]
  · have : P0 t = 1 := Finset.prod_eq_one fun i _ => ro1_one (Th_supp h i)
    rw [this, one_mul]

lemma Th_hasSum (t : Fin n → ℝ) : HasSum (fun k : Fin n → ℤ => Th (t - kR k)) 1 := by
  classical
  let T : Fin n → Finset ℤ := fun i => Finset.Icc (⌊2 * (t i / 2)⌋ - 2) (⌊2 * (t i / 2)⌋ + 2)
  have e : ∀ k : Fin n → ℤ, Th (t - kR k) = ∏ i, psi (t i / 2 - (k i : ℝ) / 2) := by
    intro k
    simp only [Th, th1, kR, Pi.sub_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1; ring
  simp_rw [e]
  have hval : ∑ k ∈ Fintype.piFinset T, ∏ i, psi (t i / 2 - (k i : ℝ) / 2) = 1 := by
    rw [← Finset.prod_univ_sum (t := T) (f := fun i k => psi (t i / 2 - (k : ℝ) / 2))]
    exact Finset.prod_eq_one fun i _ => psi_sum_Icc (t i / 2)
  rw [← hval]
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  rw [Fintype.mem_piFinset, not_forall] at hk
  obtain ⟨i, hi⟩ := hk
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply psi_zero
  have h1 : ((⌊2 * (t i / 2)⌋ : ℤ) : ℝ) ≤ 2 * (t i / 2) := Int.floor_le _
  have h2 : 2 * (t i / 2) < ⌊2 * (t i / 2)⌋ + 1 := Int.lt_floor_add_one _
  simp only [T, Finset.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hk | hk
  · have : (k i : ℝ) ≤ ⌊2 * (t i / 2)⌋ - 3 := by exact_mod_cast (by omega : k i ≤ ⌊2 * (t i / 2)⌋ - 3)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (⌊2 * (t i / 2)⌋ : ℝ) + 3 ≤ k i := by exact_mod_cast (by omega : ⌊2 * (t i / 2)⌋ + 3 ≤ k i)
    rw [abs_of_neg (by linarith)]
    linarith

end

end Aux_ESF


namespace Aux_ESF

open MasulloGRH Topology Filter Set Aux_SEN

noncomputable section

variable {m n r s : ℕ} {d : Fin s → ℕ}

abbrev YY (r s : ℕ) := (Fin r → ℝ) × (Fin s → ℝ)
abbrev WW (m n r s : ℕ) := (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℝ) × (Fin s → ℝ)
abbrev LL (r s : ℕ) (d : Fin s → ℕ) := (Fin r → ℤ) × ((i : Fin s) → ZMod (d i))

def iota (l : LL r s d) : YY r s := (fun i => (l.1 i : ℝ), fun i => ((l.2 i).val : ℝ))

def near (y : YY r s) : LL r s d :=
  (fun i => round (y.1 i), fun i => ((round (y.2 i) : ℤ) : ZMod (d i)))

lemma round_of_near {y : ℝ} {z : ℤ} (h : |y - z| < 1 / 2) : round y = z := by
  rw [round_eq, Int.floor_eq_iff]
  rw [abs_lt] at h
  constructor <;> linarith

lemma near_eq (hd : ∀ i, d i ≠ 0) (l : LL r s d) (y : YY r s)
    (h1 : ∀ i, |y.1 i - l.1 i| < 1 / 2) (h2 : ∀ i, |y.2 i - (l.2 i).val| < 1 / 2) :
    near y = l := by
  refine Prod.ext (funext fun i => round_of_near (h1 i)) (funext fun i => ?_)
  haveI : NeZero (d i) := ⟨hd i⟩
  show ((round (y.2 i) : ℤ) : ZMod (d i)) = l.2 i
  have := round_of_near (z := ((l.2 i).val : ℤ)) (by exact_mod_cast h2 i)
  rw [this, Int.cast_natCast, ZMod.natCast_zmod_val]

lemma near_iota (hd : ∀ i, d i ≠ 0) (l : LL r s d) : near (iota l) = l :=
  near_eq hd l _ (fun i => by simp [iota]) (fun i => by simp [iota])

/-- the bump in the `(t, y)`-variables -/
def Bt (v : (Fin n → ℝ) × YY r s) : ℂ :=
  ((Th v.1 * ((∏ i, be1 (v.2.1 i)) * ∏ i, be1 (v.2.2 i)) : ℝ) : ℂ)

lemma Bt_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Bt (n := n) (r := r) (s := s)) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : (Fin n → ℝ) × YY r s => Th v.1 * ((∏ i, be1 (v.2.1 i)) * ∏ i, be1 (v.2.2 i))) := by
    refine (Th_smooth.comp contDiff_fst).mul ((contDiff_prod fun i _ => ?_).mul
      (contDiff_prod fun i _ => ?_))
    · exact be1_smooth.comp ((coordR_smooth i).comp (contDiff_fst.comp contDiff_snd))
    · exact be1_smooth.comp ((coordR_smooth i).comp (contDiff_snd.comp contDiff_snd))
  exact Complex.ofRealCLM.contDiff.comp h1

lemma Bt_supp {v : (Fin n → ℝ) × YY r s} (h : Bt v ≠ 0) :
    (∀ i, |v.1 i| < 3 / 4) ∧ (∀ i, |v.2.1 i| < 7 / 64) ∧ (∀ i, |v.2.2 i| < 7 / 64) := by
  simp only [Bt, ne_eq, Complex.ofReal_eq_zero, mul_eq_zero, not_or] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨Th_supp h1, fun i => be1_supp (Finset.prod_ne_zero_iff.1 h2 i (Finset.mem_univ i)),
    fun i => be1_supp (Finset.prod_ne_zero_iff.1 h3 i (Finset.mem_univ i))⟩

lemma Bt_cs : HasCompactSupport (Bt (n := n) (r := r) (s := s)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : (Fin n → ℝ) × YY r s) 1) fun v hv => ?_
  by_contra h
  obtain ⟨h1, h2, h3⟩ := Bt_supp h
  apply hv
  rw [mem_closedBall_zero_iff]
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      rw [Real.norm_eq_abs]; linarith [h1 i]
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      rw [Real.norm_eq_abs]; linarith [h2 i]
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      rw [Real.norm_eq_abs]; linarith [h3 i]

lemma Bt_zero_y (t : Fin n → ℝ) : Bt (t, (0 : YY r s)) = (Th t : ℂ) := by
  simp [Bt, be1_zero]

/-- projections -/
def prXT : WW m n r s →L[ℝ] XT m n :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

def prTY : WW m n r s →L[ℝ] (Fin n → ℝ) × YY r s := ContinuousLinearMap.snd ℝ _ _

lemma prXT_apply (w : WW m n r s) : prXT w = (w.1, w.2.1) := rfl
lemma prTY_apply (w : WW m n r s) : prTY w = w.2 := rfl

lemma norm_prXT : ‖(prXT : WW m n r s →L[ℝ] XT m n)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul, prXT_apply]
  refine norm_prod_le_iff.2 ⟨norm_fst_le w, (norm_fst_le w.2).trans (norm_snd_le w)⟩

lemma norm_prTY : ‖(prTY : WW m n r s →L[ℝ] (Fin n → ℝ) × YY r s)‖ ≤ 1 :=
  ContinuousLinearMap.norm_snd_le _ _ _

/-- the bump on `W`, centred at the lattice point `l` -/
def Bl (l : LL r s d) (w : WW m n r s) : ℂ := Bt (prTY w - ((0 : Fin n → ℝ), iota l))

lemma Bl_smooth (l : LL r s d) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Bl (m := m) (n := n) l) :=
  Bt_smooth.comp (prTY.contDiff.sub contDiff_const)

lemma Bl_bound (k : ℕ) : ∃ M, 0 ≤ M ∧ ∀ (l : LL r s d) (i : ℕ), i ≤ k → ∀ w : WW m n r s,
    ‖iteratedFDeriv ℝ i (Bl l) w‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := cs_boundG (Bt_smooth (n := n) (r := r) (s := s)) Bt_cs k
  refine ⟨M, hM0, fun l i hi w => ?_⟩
  have e : Bl (m := m) l = (fun v => Bt (v - ((0 : Fin n → ℝ), iota l))) ∘ prTY := rfl
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => Bt (v - ((0 : Fin n → ℝ), iota l))) :=
    Bt_smooth.comp (contDiff_id.sub contDiff_const)
  rw [e]
  refine (norm_comp_clm_le hs _ norm_prTY i w).trans ?_
  rw [iteratedFDeriv_comp_sub' i]
  exact hM i hi _

lemma Bl_supp {l : LL r s d} {w : WW m n r s} (h : Bl l w ≠ 0) :
    (∀ i, |w.2.1 i| < 3 / 4) ∧ (∀ i, |w.2.2.1 i - l.1 i| < 7 / 64) ∧
      (∀ i, |w.2.2.2 i - (l.2 i).val| < 7 / 64) := by
  have := Bt_supp h
  simpa [prTY_apply, iota] using this

lemma near_of_Bl (hd : ∀ i, d i ≠ 0) {l : LL r s d} {w : WW m n r s} (h : Bl l w ≠ 0)
    (y : YY r s) (h1 : ∀ i, |y.1 i - w.2.2.1 i| < 3 / 8) (h2 : ∀ i, |y.2 i - w.2.2.2 i| < 3 / 8) :
    near y = l := by
  obtain ⟨-, ha, hb⟩ := Bl_supp h
  refine near_eq hd l y (fun i => ?_) (fun i => ?_)
  · have := abs_sub_le (y.1 i) (w.2.2.1 i) (l.1 i)
    linarith [h1 i, ha i]
  · have := abs_sub_le (y.2 i) (w.2.2.2 i) ((l.2 i).val : ℝ)
    linarith [h2 i, hb i]

/-- the function `R g` on `W` -/
def Rfun (g : ES m n r s d) (w : WW m n r s) : ℂ :=
  Bl (near (d := d) w.2.2) w * elemLift g.toFun (near (d := d) w.2.2).1 (near (d := d) w.2.2).2 (prXT w)

/-- the local model of `R g` near points whose `y`-coordinate rounds to `l` -/
def Gl (g : ES m n r s d) (l : LL r s d) (w : WW m n r s) : ℂ :=
  Bl l w * elemLift g.toFun l.1 l.2 (prXT w)

lemma Gl_smooth (g : ES m n r s d) (l : LL r s d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gl g l) :=
  (Bl_smooth l).mul ((lift_smooth g l.1 l.2).comp prXT.contDiff)

lemma coord_close {w w0 : WW m n r s} (h : dist w w0 < 1 / 8) :
    (∀ i, |w.2.2.1 i - w0.2.2.1 i| < 1 / 8) ∧ (∀ i, |w.2.2.2 i - w0.2.2.2 i| < 1 / 8) := by
  rw [dist_eq_norm] at h
  have h1 : ‖w.2.2 - w0.2.2‖ < 1 / 8 :=
    lt_of_le_of_lt ((norm_snd_le (w.2 - w0.2)).trans (norm_snd_le (w - w0))) h
  constructor
  · intro i
    have := (norm_le_pi_norm (w.2.2.1 - w0.2.2.1) i).trans (norm_fst_le (w.2.2 - w0.2.2))
    rw [Real.norm_eq_abs] at this
    simpa using lt_of_le_of_lt this h1
  · intro i
    have := (norm_le_pi_norm (w.2.2.2 - w0.2.2.2) i).trans (norm_snd_le (w.2.2 - w0.2.2))
    rw [Real.norm_eq_abs] at this
    simpa using lt_of_le_of_lt this h1

lemma Rfun_loc (hd : ∀ i, d i ≠ 0) (g : ES m n r s d) (w0 : WW m n r s) :
    Rfun g =ᶠ[𝓝 w0] Gl g (near w0.2.2) := by
  filter_upwards [Metric.ball_mem_nhds w0 (by norm_num : (0 : ℝ) < 1 / 8)] with w hw
  obtain ⟨c1, c2⟩ := coord_close hw
  by_cases hn : near w.2.2 = (near w0.2.2 : LL r s d)
  · simp only [Rfun, Gl, hn]
  · have e1 : Bl (near (d := d) w.2.2) w = 0 := by
      by_contra h
      apply hn
      exact (near_of_Bl hd h w0.2.2 (fun i => by rw [abs_sub_comm]; linarith [c1 i])
        (fun i => by rw [abs_sub_comm]; linarith [c2 i])).symm
    have e2 : Bl (near w0.2.2 : LL r s d) w = 0 := by
      by_contra h
      exact hn (near_of_Bl hd h w.2.2 (fun i => by simp) (fun i => by simp))
    simp only [Rfun, Gl, e1, e2, zero_mul]

lemma Rfun_smooth (hd : ∀ i, d i ≠ 0) (g : ES m n r s d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Rfun g) :=
  contDiff_iff_contDiffAt.2 fun w0 =>
    (Gl_smooth g _).contDiffAt.congr_of_eventuallyEq (Rfun_loc hd g w0)

lemma Rfun_iter (hd : ∀ i, d i ≠ 0) (g : ES m n r s d) (k : ℕ) (w0 : WW m n r s) :
    iteratedFDeriv ℝ k (Rfun g) w0 = iteratedFDeriv ℝ k (Gl g (near w0.2.2)) w0 :=
  ((Rfun_loc hd g w0).iteratedFDeriv ℝ k).eq_of_nhds

def Dsum (d : Fin s → ℕ) : ℝ := ∑ i, (d i : ℝ)

lemma norm_intvec_le (a : Fin r → ℤ) : ‖(fun i => (a i : ℝ))‖ ≤ ‖a‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
    rw [Int.norm_cast_real]; exact norm_le_pi_norm a i

lemma norm_le_intvec (a : Fin r → ℤ) : ‖a‖ ≤ ‖(fun i => (a i : ℝ))‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
    rw [← Int.norm_cast_real]; exact norm_le_pi_norm (fun i => (a i : ℝ)) i

lemma norm_val_le (hd : ∀ i, d i ≠ 0) (b : (i : Fin s) → ZMod (d i)) :
    ‖(fun i => ((b i).val : ℝ))‖ ≤ Dsum d := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _)).2 fun i => ?_
  haveI : NeZero (d i) := ⟨hd i⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 : ((b i).val : ℝ) ≤ d i := by exact_mod_cast (ZMod.val_lt (b i)).le
  exact h1.trans (Finset.single_le_sum (f := fun i => (d i : ℝ)) (fun j _ => Nat.cast_nonneg _)
    (Finset.mem_univ i))

lemma norm_iota_le (hd : ∀ i, d i ≠ 0) (l : LL r s d) : ‖iota l‖ ≤ ‖l.1‖ + Dsum d :=
  norm_prod_le_iff.2 ⟨(norm_intvec_le l.1).trans (le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _)),
    (norm_val_le hd l.2).trans (le_add_of_nonneg_left (norm_nonneg _))⟩

/-- the closed set containing the support of `B_l` -/
lemma tsupport_Bl (hd : ∀ i, d i ≠ 0) (l : LL r s d) :
    tsupport (Bl (m := m) (n := n) l) ⊆ {w | ‖w‖ ≤ ‖w.1‖ + ‖l.1‖ + (Dsum d + 1)} := by
  refine closure_minimal (fun w hw => ?_) (isClosed_le continuous_norm
    (((continuous_norm.comp continuous_fst).add continuous_const).add continuous_const :
      Continuous fun w : WW m n r s => ‖w.1‖ + ‖l.1‖ + (Dsum d + 1)))
  obtain ⟨h1, h2, h3⟩ := Bl_supp hw
  have ht : ‖w.2.1‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    rw [Real.norm_eq_abs]; linarith [h1 i]
  have hy : ‖w.2.2 - iota l‖ ≤ 1 := by
    refine norm_prod_le_iff.2 ⟨(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_,
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_⟩
    · simp only [Prod.fst_sub, Pi.sub_apply, iota, Real.norm_eq_abs]; linarith [h2 i]
    · simp only [Prod.snd_sub, Pi.sub_apply, iota, Real.norm_eq_abs]; linarith [h3 i]
  have hy2 : ‖w.2.2‖ ≤ ‖l.1‖ + Dsum d + 1 := by
    have := norm_le_norm_add_norm_sub' (w.2.2) (iota l)
    have := norm_iota_le hd l
    have : ‖w.2.2‖ ≤ ‖iota l‖ + ‖w.2.2 - iota l‖ := by
      have := norm_add_le (iota l) (w.2.2 - iota l); simpa using this
    linarith
  show ‖w‖ ≤ ‖w.1‖ + ‖l.1‖ + (Dsum d + 1)
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · have := Dsum d; have : 0 ≤ Dsum d := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    have := norm_nonneg l.1; linarith
  · have : 0 ≤ Dsum d := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    have := norm_nonneg l.1; have := norm_nonneg w.1; linarith
  · have := norm_nonneg w.1; linarith

/-- the finite set of seminorm indices used to bound `R` -/
def sR (M k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.range (M + 1) ×ˢ Finset.range (M + 1) ×ˢ Finset.range (k + 1)

lemma Rfun_bound (hd : ∀ i, d i ≠ 0) (M k : ℕ) : ∃ C, 0 ≤ C ∧ ∀ (g : ES m n r s d) (w : WW m n r s),
    ‖w‖ ^ M * ‖iteratedFDeriv ℝ k (Rfun g) w‖ ≤ C * (sR M k).sup sn g := by
  obtain ⟨MB, hMB0, hMB⟩ := Bl_bound (m := m) (r := r) (d := d) (n := n) k
  set K := Dsum d + 1 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Dsum d := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    linarith
  refine ⟨3 ^ M * (2 ^ k * MB * ((k + 1) * (2 + K ^ M))), by positivity, fun g w => ?_⟩
  set l : LL r s d := near w.2.2
  set S := (sR M k).sup sn g
  have hS0 : 0 ≤ S := apply_nonneg _ _
  rw [Rfun_iter hd g k w]
  by_cases hz : iteratedFDeriv ℝ k (Gl g l) w = 0
  · rw [hz, norm_zero, mul_zero]; positivity
  have hw : w ∈ tsupport (Bl (m := m) (n := n) l) := by
    have h1 := support_iteratedFDeriv_subset (𝕜 := ℝ) k (f := Gl g l) hz
    exact tsupport_mul_subset_left h1
  have hwn := tsupport_Bl hd l hw
  simp only [mem_setOf_eq] at hwn
  -- derivative bound
  set x0 : XT m n := prXT w
  have hsnle : ∀ p ∈ sR M k, sn p g ≤ S := fun p hp => Seminorm.le_finset_sup_apply hp
  let B : ℝ := ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j (elemLift g.toFun l.1 l.2) x0‖
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hD : ‖iteratedFDeriv ℝ k (Gl g l) w‖ ≤ 2 ^ k * MB * B := by
    refine leibG (Bl_smooth l) ((lift_smooth g l.1 l.2).comp prXT.contDiff) w
      (fun i hi => hMB l i hi w) (fun j hj => ?_) hMB0 hB0
    refine (norm_comp_clm_le (lift_smooth g l.1 l.2) prXT norm_prXT j w).trans ?_
    exact Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j (elemLift g.toFun l.1 l.2) x0‖)
      (fun j _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  -- weight bound
  have hxw : ‖w.1‖ = ‖x0.1‖ := rfl
  have hW : ‖w‖ ^ M ≤ 3 ^ M * (‖x0.1‖ ^ M + ‖l.1‖ ^ M + K ^ M) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) hwn M).trans ?_
    rw [hxw]
    exact pow3_le _ _ _ (norm_nonneg _) (norm_nonneg _) hK0 M
  have hBS : (‖x0.1‖ ^ M + ‖l.1‖ ^ M + K ^ M) * B ≤ (k + 1) * (2 + K ^ M) * S := by
    have : ∀ j ∈ Finset.range (k + 1), (‖x0.1‖ ^ M + ‖l.1‖ ^ M + K ^ M) *
        ‖iteratedFDeriv ℝ j (elemLift g.toFun l.1 l.2) x0‖ ≤ (2 + K ^ M) * S := by
      intro j hj
      have hj' : j < k + 1 := Finset.mem_range.1 hj
      have e1 := le_sn (M, 0, j) g (l.1, l.2, x0)
      have e2 := le_sn (0, M, j) g (l.1, l.2, x0)
      have e3 := le_sn (0, 0, j) g (l.1, l.2, x0)
      simp only [pow_zero, one_mul, mul_one] at e1 e2 e3
      have s1 := hsnle (M, 0, j) (by simp [sR]; omega)
      have s2 := hsnle (0, M, j) (by simp [sR]; omega)
      have s3 := hsnle (0, 0, j) (by simp [sR]; omega)
      have hKM : 0 ≤ K ^ M := pow_nonneg hK0 M
      have := mul_le_mul_of_nonneg_left (e3.trans s3) hKM
      nlinarith
    calc (‖x0.1‖ ^ M + ‖l.1‖ ^ M + K ^ M) * B
        = ∑ j ∈ Finset.range (k + 1), (‖x0.1‖ ^ M + ‖l.1‖ ^ M + K ^ M) *
            ‖iteratedFDeriv ℝ j (elemLift g.toFun l.1 l.2) x0‖ := Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ Finset.range (k + 1), (2 + K ^ M) * S := Finset.sum_le_sum this
      _ = (k + 1) * (2 + K ^ M) * S := by rw [Finset.sum_const, Finset.card_range]; simp; ring
  calc ‖w‖ ^ M * ‖iteratedFDeriv ℝ k (Gl g l) w‖
      ≤ (3 ^ M * (‖x0.1‖ ^ M + ‖l.1‖ ^ M + K ^ M)) * (2 ^ k * MB * B) :=
        mul_le_mul hW hD (norm_nonneg _) (by positivity)
    _ = 3 ^ M * (2 ^ k * MB) * ((‖x0.1‖ ^ M + ‖l.1‖ ^ M + K ^ M) * B) := by ring
    _ ≤ 3 ^ M * (2 ^ k * MB) * ((k + 1) * (2 + K ^ M) * S) :=
        mul_le_mul_of_nonneg_left hBS (by positivity)
    _ = 3 ^ M * (2 ^ k * MB * ((k + 1) * (2 + K ^ M))) * S := by ring

end

end Aux_ESF


namespace Aux_ESF

open MasulloGRH Topology Filter Set Aux_SEN

noncomputable section

variable {m n r s : ℕ} {d : Fin s → ℕ}

/-! ### the map `R : S(ℝ^m × 𝕋^n × ℤ^r × F) → 𝓢(W)` -/

def Rs (hd : ∀ i, d i ≠ 0) (g : ES m n r s d) : SchwartzMap (WW m n r s) ℂ where
  toFun := Rfun g
  smooth' := Rfun_smooth hd g
  decay' M k := by
    obtain ⟨C, -, hC⟩ := Rfun_bound (m := m) (n := n) hd M k
    exact ⟨C * (sR M k).sup sn g, hC g⟩

lemma Rs_apply (hd : ∀ i, d i ≠ 0) (g : ES m n r s d) (w : WW m n r s) : Rs hd g w = Rfun g w := rfl

def Rlin (hd : ∀ i, d i ≠ 0) : ES m n r s d →ₗ[ℂ] SchwartzMap (WW m n r s) ℂ where
  toFun := Rs hd
  map_add' f g := by
    ext w
    simp only [Rs_apply, SchwartzMap.add_apply, Rfun]
    rw [lift_add, Pi.add_apply, mul_add]
  map_smul' c g := by
    ext w
    simp only [Rs_apply, SchwartzMap.smul_apply, Rfun, RingHom.id_apply]
    rw [lift_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

def Rclm (hd : ∀ i, d i ≠ 0) : ES m n r s d →L[ℂ] SchwartzMap (WW m n r s) ℂ where
  toLinearMap := Rlin hd
  cont := by
    refine Seminorm.continuous_from_bounded es_ws (schwartz_withSeminorms ℂ (WW m n r s) ℂ)
      (Rlin hd) fun ⟨M, k⟩ => ?_
    obtain ⟨C, hC0, hC⟩ := Rfun_bound (m := m) (n := n) hd M k
    refine ⟨sR M k, ⟨C, hC0⟩, fun g => ?_⟩
    simp only [Seminorm.comp_apply, SchwartzMap.schwartzSeminormFamily_apply, Seminorm.smul_apply,
      NNReal.smul_def, smul_eq_mul, NNReal.coe_mk]
    exact SchwartzMap.seminorm_le_bound ℂ M k _ (mul_nonneg hC0 (apply_nonneg _ _)) fun w => hC g w

lemma Rclm_apply (hd : ∀ i, d i ≠ 0) (g : ES m n r s d) (w : WW m n r s) :
    Rclm hd g w = Rfun g w := rfl

/-! ### the map `P : 𝓢(W) → S(ℝ^m × 𝕋^n × ℤ^r × F)` (periodisation and restriction) -/

def Lin : XT m n →L[ℝ] WW m n r s :=
  (ContinuousLinearMap.fst ℝ _ _).prod ((ContinuousLinearMap.snd ℝ _ _).prod 0)

lemma Lin_apply (v : XT m n) : (Lin v : WW m n r s) = (v.1, v.2, 0) := rfl

lemma norm_Lin : ‖(Lin : XT m n →L[ℝ] WW m n r s)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, Lin_apply]
  refine norm_prod_le_iff.2 ⟨norm_fst_le v, norm_prod_le_iff.2 ⟨norm_snd_le v, by simp⟩⟩

def ck (k : Fin n → ℤ) (l : LL r s d) : WW m n r s := (0, -kR k, iota l)

def P0c (t : Fin n → ℝ) : ℂ := ((P0 t : ℝ) : ℂ)

def P0b (v : XT m n) : ℂ := P0c v.2

lemma P0c_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P0c (n := n)) :=
  Complex.ofRealCLM.contDiff.comp P0_smooth

lemma P0c_cs : HasCompactSupport (P0c (n := n)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) 1) fun t ht => ?_
  by_contra h
  apply ht
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  have h' : P0 t ≠ 0 := fun h0 => h (by simp [P0c, h0])
  rw [Real.norm_eq_abs]; linarith [P0_supp h' i]

lemma P0b_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P0b (m := m) (n := n)) :=
  P0c_smooth.comp contDiff_snd

lemma P0b_bound (K : ℕ) : ∃ M, 0 ≤ M ∧ ∀ (k : Fin n → ℤ) (i : ℕ), i ≤ K → ∀ v : XT m n,
    ‖iteratedFDeriv ℝ i (fun v => P0b (v - ((0 : Fin m → ℝ), kR k))) v‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := cs_boundG (P0c_smooth (n := n)) P0c_cs K
  refine ⟨M, hM0, fun k i hi v => ?_⟩
  rw [iteratedFDeriv_comp_sub' i]
  have := norm_comp_clm_le (P0c_smooth (n := n)) (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin n → ℝ))
    (ContinuousLinearMap.norm_snd_le _ _ _) i (v - ((0 : Fin m → ℝ), kR k))
  exact this.trans (hM i hi _)

/-- one term of the periodisation -/
def term (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) (k : Fin n → ℤ) (v : XT m n) : ℂ :=
  P0b (v - ((0 : Fin m → ℝ), kR k)) * h (Lin v + ck k l)

lemma term_smooth (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) (k : Fin n → ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (term h l k) :=
  (P0b_smooth.comp (contDiff_id.sub contDiff_const)).mul
    ((h.smooth ⊤).comp (Lin.contDiff.add contDiff_const))

/-- the periodisation in the torus variables, restricted to the lattice point `l` -/
def Per (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) (v : XT m n) : ℂ := ∑' k, term h l k v

def Kset (v0 : XT m n) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (⌊v0.2 i⌋ - 1) (⌊v0.2 i⌋ + 2)

lemma term_zero (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) {v v0 : XT m n}
    (hv : dist v v0 < 1 / 16) {k : Fin n → ℤ} (hk : k ∉ Kset v0) : term h l k v = 0 := by
  by_contra hne
  apply hk
  have hP : P0 (v.2 - kR k) ≠ 0 := by
    intro h0
    apply hne
    simp [term, P0b, P0c, h0]
  rw [Kset, Fintype.mem_piFinset]
  intro i
  have h1 := P0_supp hP i
  simp only [Pi.sub_apply, kR] at h1
  have h2 : |v.2 i - v0.2 i| < 1 / 16 := by
    rw [dist_eq_norm] at hv
    have := (norm_le_pi_norm (v.2 - v0.2) i).trans (norm_snd_le (v - v0))
    rw [Real.norm_eq_abs] at this
    simpa using lt_of_le_of_lt this hv
  rw [abs_lt] at h1 h2
  have f1 : ((⌊v0.2 i⌋ : ℤ) : ℝ) ≤ v0.2 i := Int.floor_le _
  have f2 : v0.2 i < ⌊v0.2 i⌋ + 1 := Int.lt_floor_add_one _
  have a1 : ((⌊v0.2 i⌋ - 1 : ℤ) : ℝ) < k i := by push_cast; linarith
  have a2 : (k i : ℝ) < ((⌊v0.2 i⌋ + 2 : ℤ) : ℝ) := by push_cast; linarith
  have b1 : ⌊v0.2 i⌋ - 1 < k i := by exact_mod_cast a1
  have b2 : k i < ⌊v0.2 i⌋ + 2 := by exact_mod_cast a2
  rw [Finset.mem_Icc]; omega

lemma Per_eq_sum (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) {v v0 : XT m n}
    (hv : dist v v0 < 1 / 16) : Per h l v = ∑ k ∈ Kset v0, term h l k v :=
  tsum_eq_sum fun k hk => term_zero h l hv hk

lemma Per_loc (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) (v0 : XT m n) :
    Per h l =ᶠ[𝓝 v0] fun v => ∑ k ∈ Kset v0, term h l k v := by
  filter_upwards [Metric.ball_mem_nhds v0 (by norm_num : (0 : ℝ) < 1 / 16)] with v hv
  exact Per_eq_sum h l hv

lemma Per_smooth (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Per h l) :=
  contDiff_iff_contDiffAt.2 fun v0 =>
    (ContDiff.sum fun k _ => term_smooth h l k).contDiffAt.congr_of_eventuallyEq (Per_loc h l v0)

lemma Per_iter (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) (K : ℕ) (v0 : XT m n) :
    iteratedFDeriv ℝ K (Per h l) v0 = ∑ k ∈ Kset v0, iteratedFDeriv ℝ K (term h l k) v0 := by
  rw [((Per_loc h l v0).iteratedFDeriv ℝ K).eq_of_nhds,
    iteratedFDeriv_sum fun k _ => (term_smooth h l k).of_le (by exact_mod_cast le_top)]
  simp

lemma card_Kset (v0 : XT m n) : ((Kset v0).card : ℝ) = 4 ^ n := by
  rw [Kset, Fintype.card_piFinset]
  have : ∀ i : Fin n, (Finset.Icc (⌊v0.2 i⌋ - 1) (⌊v0.2 i⌋ + 2)).card = 4 := by
    intro i
    rw [Int.card_Icc]
    have : ⌊v0.2 i⌋ + 2 + 1 - (⌊v0.2 i⌋ - 1) = 4 := by ring
    rw [this]; rfl
  simp [this]

/-- the main estimate for the periodisation -/
lemma Per_bound (K : ℕ) : ∃ C, 0 ≤ C ∧ ∀ (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d)
    (I J : ℕ) (v0 : XT m n), ‖l.1‖ ^ J * ‖v0.1‖ ^ I * ‖iteratedFDeriv ℝ K (Per h l) v0‖ ≤
      C * ∑ j ∈ Finset.range (K + 1), SchwartzMap.seminorm ℂ (I + J) j h := by
  obtain ⟨MP, hMP0, hMP⟩ := P0b_bound (m := m) (n := n) K
  refine ⟨4 ^ n * (2 ^ K * MP), by positivity, fun h l I J v0 => ?_⟩
  set S := ∑ j ∈ Finset.range (K + 1), SchwartzMap.seminorm ℂ (I + J) j h
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => apply_nonneg _ _
  have hwt : 0 ≤ ‖l.1‖ ^ J * ‖v0.1‖ ^ I := by positivity
  have hk : ∀ k ∈ Kset v0, ‖l.1‖ ^ J * ‖v0.1‖ ^ I * ‖iteratedFDeriv ℝ K (term h l k) v0‖ ≤
      2 ^ K * MP * S := by
    intro k _
    set w : WW m n r s := Lin v0 + ck k l
    have hw1 : ‖v0.1‖ ≤ ‖w‖ := by
      have : w.1 = v0.1 := by simp [w, Lin_apply, ck]
      rw [← this]; exact norm_fst_le w
    have hw2 : ‖l.1‖ ≤ ‖w‖ := by
      have : w.2.2 = iota l := by simp [w, Lin_apply, ck]
      refine (norm_le_intvec l.1).trans ?_
      refine (norm_fst_le (iota l)).trans ?_
      rw [← this]
      exact (norm_snd_le w.2).trans (norm_snd_le w)
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((fun z => h (z + ck k l)) ∘ Lin) :=
      ((h.smooth ⊤).comp (contDiff_id.add contDiff_const)).comp Lin.contDiff
    have hD : ‖iteratedFDeriv ℝ K (term h l k) v0‖ ≤ 2 ^ K * MP *
        ∑ j ∈ Finset.range (K + 1), ‖iteratedFDeriv ℝ j h w‖ := by
      refine leibG (P0b_smooth.comp (contDiff_id.sub contDiff_const)) hsm v0
        (fun i hi => hMP k i hi v0) (fun j hj => ?_) hMP0
        (Finset.sum_nonneg fun j _ => norm_nonneg _)
      have hs2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => h (z + ck k l)) :=
        (h.smooth ⊤).comp (contDiff_id.add contDiff_const)
      refine (norm_comp_clm_le hs2 Lin norm_Lin j v0).trans ?_
      rw [iteratedFDeriv_comp_add_right]
      exact Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j h w‖)
        (fun j _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
    have hW : ‖l.1‖ ^ J * ‖v0.1‖ ^ I ≤ ‖w‖ ^ (I + J) := by
      rw [pow_add, mul_comm]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw1 I)
        (pow_le_pow_left₀ (norm_nonneg _) hw2 J) (by positivity) (by positivity)
    calc ‖l.1‖ ^ J * ‖v0.1‖ ^ I * ‖iteratedFDeriv ℝ K (term h l k) v0‖
        ≤ ‖l.1‖ ^ J * ‖v0.1‖ ^ I * (2 ^ K * MP *
            ∑ j ∈ Finset.range (K + 1), ‖iteratedFDeriv ℝ j h w‖) :=
          mul_le_mul_of_nonneg_left hD hwt
      _ = 2 ^ K * MP * ∑ j ∈ Finset.range (K + 1),
            ‖l.1‖ ^ J * ‖v0.1‖ ^ I * ‖iteratedFDeriv ℝ j h w‖ := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 2 ^ K * MP * S := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
          exact (mul_le_mul_of_nonneg_right hW (norm_nonneg _)).trans
            (SchwartzMap.le_seminorm ℂ (I + J) j h w)
  rw [Per_iter]
  calc ‖l.1‖ ^ J * ‖v0.1‖ ^ I * ‖∑ k ∈ Kset v0, iteratedFDeriv ℝ K (term h l k) v0‖
      ≤ ‖l.1‖ ^ J * ‖v0.1‖ ^ I * ∑ k ∈ Kset v0, ‖iteratedFDeriv ℝ K (term h l k) v0‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hwt
    _ = ∑ k ∈ Kset v0, ‖l.1‖ ^ J * ‖v0.1‖ ^ I * ‖iteratedFDeriv ℝ K (term h l k) v0‖ :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ k ∈ Kset v0, 2 ^ K * MP * S := Finset.sum_le_sum hk
    _ = 4 ^ n * (2 ^ K * MP) * S := by
        rw [Finset.sum_const, nsmul_eq_mul, card_Kset]; ring

/-- periodicity -/
lemma Per_periodic (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) (x : Fin m → ℝ)
    (t : Fin n → ℝ) (j : Fin n → ℤ) : Per h l (x, t + kR j) = Per h l (x, t) := by
  have e : ∀ k, term h l k (x, t + kR j) = term h l (k - j) (x, t) := by
    intro k
    have e1 : ((x, t + kR j) : XT m n) - ((0 : Fin m → ℝ), kR k) =
        (x, t) - ((0 : Fin m → ℝ), kR (k - j)) := by
      ext i <;> simp [kR]; ring
    have e2 : (Lin (x, t + kR j) : WW m n r s) + ck k l = Lin (x, t) + ck (k - j) l := by
      ext i <;> simp [Lin_apply, ck, kR]; ring
    simp only [term, e1, e2]
  simp only [Per, e]
  exact (Equiv.subRight j).tsum_eq (fun k => term h l k (x, t))

lemma rep_shift (t : Fin n → ℝ) : ∃ j : Fin n → ℤ,
    (fun i => rep ((t i : ℝ) : UnitAddCircle)) = t + kR j := by
  have : ∀ i, ∃ z : ℤ, rep ((t i : ℝ) : UnitAddCircle) = t i + z := by
    intro i
    have h := coe_rep ((t i : ℝ) : UnitAddCircle)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨-z, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hz
    push_cast; linarith
  choose j hj using this
  exact ⟨j, funext fun i => by simp [hj i, kR]⟩

/-- the function `P h` on the elementary group -/
def Pfun (h : SchwartzMap (WW m n r s) ℂ) (z : ElemGroup m n r s d) : ℂ :=
  Per h (z.2.2.1, z.2.2.2) (z.1, fun i => rep (z.2.1 i))

lemma lift_Pfun (h : SchwartzMap (WW m n r s) ℂ) (a : Fin r → ℤ) (b : (i : Fin s) → ZMod (d i)) :
    elemLift (Pfun h) a b = Per h (a, b) := by
  funext xt
  obtain ⟨j, hj⟩ := rep_shift xt.2
  show Per h (a, b) (xt.1, fun i => rep ((xt.2 i : ℝ) : UnitAddCircle)) = Per h (a, b) xt
  rw [hj, Per_periodic]

lemma Pfun_rd (h : SchwartzMap (WW m n r s) ℂ) : IsRapidDecay (Pfun (d := d) h) := by
  refine ⟨fun a b => by rw [lift_Pfun]; exact Per_smooth h (a, b), fun i j k => ?_⟩
  obtain ⟨C, -, hC⟩ := Per_bound (m := m) (n := n) (r := r) (s := s) (d := d) k
  refine ⟨C * ∑ j' ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ (i + j) j' h, fun a b xt => ?_⟩
  rw [lift_Pfun]
  exact hC h (a, b) i j xt

def Ps (h : SchwartzMap (WW m n r s) ℂ) : ES m n r s d :=
  ⟨Pfun h, Submodule.subset_span (Pfun_rd h)⟩

lemma Ps_toFun (h : SchwartzMap (WW m n r s) ℂ) : (Ps (d := d) h).toFun = Pfun h := rfl

lemma Per_add (h1 h2 : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) (v : XT m n) :
    Per (h1 + h2) l v = Per h1 l v + Per h2 l v := by
  have hv : dist v v < 1 / 16 := by rw [dist_self]; norm_num
  rw [Per_eq_sum _ l hv, Per_eq_sum _ l hv, Per_eq_sum _ l hv, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [term, SchwartzMap.add_apply, mul_add]

lemma Per_smul (c : ℂ) (h : SchwartzMap (WW m n r s) ℂ) (l : LL r s d) (v : XT m n) :
    Per (c • h) l v = c * Per h l v := by
  have hv : dist v v < 1 / 16 := by rw [dist_self]; norm_num
  rw [Per_eq_sum _ l hv, Per_eq_sum _ l hv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [term, SchwartzMap.smul_apply, smul_eq_mul]
  ring

lemma es_ext {f g : ES m n r s d} (h : ∀ z, f.toFun z = g.toFun z) : f = g :=
  Subtype.ext (funext h)

def Plin : SchwartzMap (WW m n r s) ℂ →ₗ[ℂ] ES m n r s d where
  toFun := Ps
  map_add' h1 h2 := es_ext fun z => by
    show Pfun (h1 + h2) z = Pfun h1 z + Pfun h2 z
    exact Per_add h1 h2 _ _
  map_smul' c h := es_ext fun z => by
    show Pfun (c • h) z = c * Pfun h z
    exact Per_smul c h _ _

def sP (p : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (p.2.2 + 1)).image fun j => (p.1 + p.2.1, j)

def Pclm : SchwartzMap (WW m n r s) ℂ →L[ℂ] ES m n r s d where
  toLinearMap := Plin
  cont := by
    refine Seminorm.continuous_from_bounded (schwartz_withSeminorms ℂ (WW m n r s) ℂ) es_ws
      Plin fun p => ?_
    obtain ⟨C, hC0, hC⟩ := Per_bound (m := m) (n := n) (r := r) (s := s) (d := d) p.2.2
    refine ⟨sP p, ⟨C * (p.2.2 + 1), by positivity⟩, fun h => ?_⟩
    simp only [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul,
      NNReal.coe_mk]
    set S := (sP p).sup (schwartzSeminormFamily ℂ (WW m n r s) ℂ) h
    have hS : ∑ j ∈ Finset.range (p.2.2 + 1), SchwartzMap.seminorm ℂ (p.1 + p.2.1) j h ≤
        (p.2.2 + 1) * S := by
      calc ∑ j ∈ Finset.range (p.2.2 + 1), SchwartzMap.seminorm ℂ (p.1 + p.2.1) j h
          ≤ ∑ j ∈ Finset.range (p.2.2 + 1), S := Finset.sum_le_sum fun j hj => by
            have := Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (WW m n r s) ℂ)
              (x := h) (show (p.1 + p.2.1, j) ∈ sP p from Finset.mem_image_of_mem _ hj)
            rw [SchwartzMap.schwartzSeminormFamily_apply] at this
            exact this
        _ = (p.2.2 + 1) * S := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    refine sn_le p _ (by positivity) fun a b xt => ?_
    have := hC h (a, b) p.1 p.2.1 xt
    rw [show (Plin h : ES m n r s d) = Ps h from rfl, Ps_toFun, lift_Pfun]
    calc _ ≤ C * ∑ j ∈ Finset.range (p.2.2 + 1), SchwartzMap.seminorm ℂ (p.1 + p.2.1) j h := this
      _ ≤ C * ((p.2.2 + 1) * S) := mul_le_mul_of_nonneg_left hS hC0
      _ = C * (p.2.2 + 1) * S := by ring

lemma Pclm_toFun (h : SchwartzMap (WW m n r s) ℂ) : (Pclm (d := d) h).toFun = Pfun h := rfl

/-! ### `P ∘ R = id` -/

lemma Rfun_iota (hd : ∀ i, d i ≠ 0) (g : ES m n r s d) (l : LL r s d) (x : Fin m → ℝ)
    (t : Fin n → ℝ) :
    Rfun g ((x, t, iota l) : WW m n r s) = (Th t : ℂ) * elemLift g.toFun l.1 l.2 (x, t) := by
  have h1 : near (d := d) (iota l) = l := near_iota hd l
  show Bl (near (d := d) (iota l)) ((x, t, iota l) : WW m n r s) *
    elemLift g.toFun (near (d := d) (iota l)).1 (near (d := d) (iota l)).2
      (prXT ((x, t, iota l) : WW m n r s)) = _
  rw [h1]
  have h2 : prTY ((x, t, iota l) : WW m n r s) - ((0 : Fin n → ℝ), iota l) = (t, (0 : YY r s)) := by
    ext i <;> simp [prTY_apply]
  rw [Bl, h2, Bt_zero_y]
  rfl

lemma lift_shift (g : ES m n r s d) (a : Fin r → ℤ) (b : (i : Fin s) → ZMod (d i))
    (x : Fin m → ℝ) (zt : Fin n → UnitAddCircle) (k : Fin n → ℤ) :
    elemLift g.toFun a b (x, (fun i => rep (zt i)) - kR k) = g.toFun (x, zt, a, b) := by
  show g.toFun (x, fun j => ((((fun i => rep (zt i)) - kR k) j : ℝ) : UnitAddCircle), a, b) = _
  refine congrArg g.toFun (Prod.ext rfl (Prod.ext (funext fun j => ?_) rfl))
  simp only [Pi.sub_apply, kR]
  rw [AddCircle.coe_sub, coe_rep]
  have : (((k j : ℤ) : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨k j, by simp⟩
  rw [this, sub_zero]

lemma PR (hd : ∀ i, d i ≠ 0) (g : ES m n r s d) : Pclm (Rclm hd g) = g := by
  refine es_ext fun z => ?_
  rw [Pclm_toFun]
  obtain ⟨x, zt, a, b⟩ := z
  show Per (Rclm hd g) (a, b) (x, fun i => rep (zt i)) = g.toFun (x, zt, a, b)
  set t : Fin n → ℝ := fun i => rep (zt i) with ht
  have hterm : ∀ k : Fin n → ℤ, term (Rclm hd g) (a, b) k (x, t) =
      (Th (t - kR k) : ℂ) * g.toFun (x, zt, a, b) := by
    intro k
    have e1 : (Lin (x, t) : WW m n r s) + ck k (a, b) = (x, t - kR k, iota (a, b)) := by
      ext i <;> simp [Lin_apply, ck, sub_eq_add_neg]
    have e0 : ((x, t) : XT m n) - ((0 : Fin m → ℝ), kR k) = (x, t - kR k) := by
      ext i <;> simp
    rw [term, e1, Rclm_apply, Rfun_iota hd, e0, P0b, P0c]
    rw [ht, lift_shift, ← ht, ← mul_assoc, ← Complex.ofReal_mul, P0_Th]
  rw [Per]
  simp_rw [hterm]
  rw [tsum_mul_right]
  have := (Th_hasSum t).tsum_eq
  rw [← Complex.ofReal_tsum, this, Complex.ofReal_one, one_mul]

end

end Aux_ESF


namespace Aux_ESF

open MasulloGRH Topology Filter Set Aux_SEN Bornology

noncomputable section

/-! ### transferring a frame along a retraction -/

section transfer

variable {E X : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
variable {ι : Type*} (φ : ι → StrongDual ℂ X) (e : ι → X) (c : ι → ℝ)

lemma tr_exp (hexp : ∀ x, HasSum (fun j => φ j x • e j) x) (R : E →L[ℂ] X) (P : X →L[ℂ] E)
    (hPR : ∀ x, P (R x) = x) (x : E) :
    HasSum (fun j => ((φ j).comp R) x • P (e j)) x := by
  have := (hexp (R x)).map P P.continuous
  rw [hPR] at this
  convert this using 1
  funext j
  simp

lemma tr_dom (hdom : ∀ Q : Seminorm ℂ X, Continuous Q → ∃ Q' : Seminorm ℂ X, Continuous Q' ∧
      ∀ j x, Q (e j) * ‖φ j x‖ ≤ c j * Q' x) (R : E →L[ℂ] X) (P : X →L[ℂ] E) :
    ∀ Q : Seminorm ℂ E, Continuous Q → ∃ Q' : Seminorm ℂ E, Continuous Q' ∧
      ∀ j x, Q (P (e j)) * ‖((φ j).comp R) x‖ ≤ c j * Q' x := by
  intro Q hQ
  obtain ⟨Q'', hQ'', h⟩ := hdom (Q.comp P.toLinearMap) (hQ.comp P.continuous)
  exact ⟨Q''.comp R.toLinearMap, hQ''.comp R.continuous, fun j x => h j (R x)⟩

end transfer

/-! ### closed bounded subsets of a complete space with a frame are compact -/

section fcompact

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [CompleteSpace E] [ContinuousSMul ℂ E]
variable {κE : Type*} {pE : SeminormFamily ℂ E κE} (hE : WithSeminorms pE)
variable {ι : Type*} (φ : ι → StrongDual ℂ E) (e : ι → E) (c : ι → ℝ)
variable (hexp : ∀ x, HasSum (fun j => φ j x • e j) x)
variable (hc0 : ∀ j, 0 < c j) (hcs : Summable c)
variable (hdom : ∀ P : Seminorm ℂ E, Continuous P → ∃ P' : Seminorm ℂ E, Continuous P' ∧
  ∀ j x, P (e j) * ‖φ j x‖ ≤ c j * P' x)

include hE hexp hc0 hcs hdom in
theorem frame_compact [T2Space E] (A : Set E) (hAc : IsClosed A) (hAb : IsVonNBounded ℂ A) :
    IsCompact A := by
  classical
  have hφb : ∀ j, BddAbove (Set.range fun x : A => ‖φ j x‖) := by
    intro j
    obtain ⟨M, hM⟩ := bdd_of_cont (q := (normSeminorm ℂ ℂ).comp (φ j : E →ₗ[ℂ] ℂ))
      (continuous_norm.comp (φ j).continuous) hAb
    exact ⟨M, by rintro _ ⟨x, rfl⟩; exact hM x x.2⟩
  let ρ : ι → ℝ := fun j => ⨆ x : A, ‖φ j x‖
  have hρ0 : ∀ j, 0 ≤ ρ j := fun j => Real.iSup_nonneg fun _ => norm_nonneg _
  have hρ : ∀ j, ∀ x ∈ A, ‖φ j x‖ ≤ ρ j := fun j x hx =>
    le_ciSup (f := fun x : A => ‖φ j x‖) (hφb j) ⟨x, hx⟩
  -- bounds on the frame vectors
  have hβ : ∀ i : κE, ∃ M, 0 ≤ M ∧ ∀ j, pE i (e j) * ρ j ≤ c j * M := by
    intro i
    obtain ⟨P', hP', hdP⟩ := hdom (pE i) (hE.continuous_seminorm i)
    obtain ⟨M, hM⟩ := bdd_of_cont hP' hAb
    refine ⟨max M 0, le_max_right _ _, fun j => ?_⟩
    rw [Real.mul_iSup_of_nonneg (apply_nonneg _ _)]
    refine Real.iSup_le (fun x => ?_) (mul_nonneg (hc0 j).le (le_max_right _ _))
    exact (hdP j x).trans (mul_le_mul_of_nonneg_left ((hM x x.2).trans (le_max_left _ _))
      (hc0 j).le)
  let K : Set (ι → ℂ) := Set.univ.pi fun j => Metric.closedBall (0 : ℂ) (ρ j)
  have hK : IsCompact K := isCompact_univ_pi fun j => isCompact_closedBall _ _
  have hsumm : ∀ a ∈ K, ∀ i : κE, Summable fun j => pE i (a j • e j) := by
    intro a ha i
    obtain ⟨M, -, hM⟩ := hβ i
    refine Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) (fun j => ?_) (hcs.mul_right M)
    rw [map_smul_eq_mul]
    have haj : ‖a j‖ ≤ ρ j := mem_closedBall_zero_iff.1 (ha j (Set.mem_univ j))
    calc ‖a j‖ * pE i (e j) ≤ ρ j * pE i (e j) := mul_le_mul_of_nonneg_right haj (apply_nonneg _ _)
      _ = pE i (e j) * ρ j := mul_comm _ _
      _ ≤ c j * M := hM j
  let R : (ι → ℂ) → E := fun a => ∑' j, a j • e j
  have hR : ∀ a ∈ K, HasSum (fun j => a j • e j) (R a) := fun a ha =>
    (summable_of_sn hE _ (hsumm a ha)).hasSum
  have hsub : A ⊆ R '' K := by
    intro x hx
    refine ⟨fun j => φ j x, fun j _ => mem_closedBall_zero_iff.2 (hρ j x hx), ?_⟩
    exact (hexp x).tsum_eq
  have hcont : ContinuousOn R K := by
    intro a0 ha0
    show Tendsto R (𝓝[K] a0) (𝓝 (R a0))
    rw [hE.tendsto_nhds R (R a0)]
    intro i ε hε
    obtain ⟨M, hM0, hM⟩ := hβ i
    have hMc : Tendsto (fun J : Finset ι => ∑' j : ↥((J : Set ι)ᶜ), c j) atTop (𝓝 0) :=
      tendsto_tsum_compl_atTop_zero c
    obtain ⟨J, hJ⟩ := (hMc.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / (4 * (M + 1)) by
      positivity))).exists
    let S := ∑ j ∈ J, pE i (e j)
    let δ := ε / (4 * (S + 1))
    have hδ : 0 < δ := by positivity
    have hN : {a : ι → ℂ | ∀ j ∈ J, a j ∈ Metric.ball (a0 j) δ} ∈ 𝓝 a0 := by
      have := set_pi_mem_nhds (s := fun j => Metric.ball (a0 j) δ) J.finite_toSet
        (fun j _ => Metric.ball_mem_nhds _ hδ)
      refine Filter.mem_of_superset this fun a ha j hj => ha j hj
    filter_upwards [inter_mem_nhdsWithin K hN, self_mem_nhdsWithin] with a ha haK
    have hdiff : HasSum (fun j => (a j - a0 j) • e j) (R a - R a0) := by
      have := (hR a haK).sub (hR a0 ha0)
      convert this using 1
      all_goals first | rfl | (funext j; exact sub_smul (a j) (a0 j) (e j))
    have hb : ∀ j, pE i ((a j - a0 j) • e j) ≤ 2 * (c j * M) := by
      intro j
      rw [map_smul_eq_mul]
      have h1 : ‖a j - a0 j‖ ≤ 2 * ρ j := by
        have h2 := mem_closedBall_zero_iff.1 (haK j (Set.mem_univ j))
        have h3 := mem_closedBall_zero_iff.1 (ha0 j (Set.mem_univ j))
        linarith [norm_sub_le (a j) (a0 j)]
      calc ‖a j - a0 j‖ * pE i (e j) ≤ 2 * ρ j * pE i (e j) :=
            mul_le_mul_of_nonneg_right h1 (apply_nonneg _ _)
        _ = 2 * (pE i (e j) * ρ j) := by ring
        _ ≤ 2 * (c j * M) := mul_le_mul_of_nonneg_left (hM j) (by norm_num)
    have hs2 : Summable fun j => pE i ((a j - a0 j) • e j) :=
      Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) hb ((hcs.mul_right M).mul_left 2)
    refine lt_of_le_of_lt (sn_hasSum_le (hE.continuous_seminorm i) hdiff hs2) ?_
    rw [← hs2.sum_add_tsum_compl (s := J)]
    have h1 : ∑ j ∈ J, pE i ((a j - a0 j) • e j) ≤ δ * S := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [map_smul_eq_mul]
      have := ha.2 j hj
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact mul_le_mul_of_nonneg_right this.le (apply_nonneg _ _)
    have h2 : ∑' j : ↥((J : Set ι)ᶜ), pE i ((a j - a0 j) • e j) ≤
        ∑' j : ↥((J : Set ι)ᶜ), 2 * (c j * M) :=
      (hs2.subtype _).tsum_le_tsum (fun j => hb j) (((hcs.subtype _).mul_right M).mul_left 2)
    have h3 : ∑' j : ↥((J : Set ι)ᶜ), 2 * (c j * M) = 2 * M * ∑' j : ↥((J : Set ι)ᶜ), c j := by
      rw [← tsum_mul_left]; congr 1; funext j; ring
    have h4 : δ * S < ε / 2 := by
      show ε / (4 * (S + 1)) * S < ε / 2
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => apply_nonneg _ _
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h5 : 2 * M * ∑' j : ↥((J : Set ι)ᶜ), c j ≤ ε / 2 := by
      have hc' : 0 ≤ ∑' j : ↥((J : Set ι)ᶜ), c j := tsum_nonneg fun j => (hc0 j).le
      have := hJ.le
      calc 2 * M * ∑' j : ↥((J : Set ι)ᶜ), c j ≤ 2 * M * (ε / (4 * (M + 1))) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ ε / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    linarith
  exact (hK.image_of_continuousOn hcont).of_isClosed_subset hAc hsub

end fcompact

/-! ### the strong dual of a space with a frame is barrelled -/


end

end Aux_ESF


namespace Aux_ESF

open MasulloGRH Topology Filter Set Aux_SEN Bornology

noncomputable section

variable {m n r s : ℕ} {d : Fin s → ℕ}

abbrev NN (m n r s : ℕ) : ℕ := m + (n + (r + s))

lemma finrank_WW : Module.finrank ℝ (WW m n r s) = Module.finrank ℝ (V (NN m n r s)) := by
  simp [Module.finrank_prod, Module.finrank_fin_fun, finrank_euclideanSpace_fin]

def eW : WW m n r s ≃L[ℝ] V (NN m n r s) := ContinuousLinearEquiv.ofFinrankEq finrank_WW

def Cto : SchwartzMap (WW m n r s) ℂ →L[ℂ] Sch (NN m n r s) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eW (m := m) (n := n) (r := r) (s := s)).symm

def Cfrom : Sch (NN m n r s) →L[ℂ] SchwartzMap (WW m n r s) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eW (m := m) (n := n) (r := r) (s := s))

lemma Cfrom_Cto (h : SchwartzMap (WW m n r s) ℂ) : Cfrom (Cto h) = h := by
  ext w
  simp [Cfrom, Cto]

def Rt (hd : ∀ i, d i ≠ 0) : ES m n r s d →L[ℂ] Sch (NN m n r s) := Cto.comp (Rclm hd)

def Pt : Sch (NN m n r s) →L[ℂ] ES m n r s d := Pclm.comp Cfrom

lemma PtRt (hd : ∀ i, d i ≠ 0) (g : ES m n r s d) : Pt (Rt hd g) = g := by
  simp only [Pt, Rt, ContinuousLinearMap.comp_apply, Cfrom_Cto, PR hd]

abbrev JJ (m n r s : ℕ) := (Fin (NN m n r s) → ℤ) × (Fin (NN m n r s) → ℤ)

/-- the frame of `S(ℝ^m × 𝕋^n × ℤ^r × F)` -/
def φE (hd : ∀ i, d i ≠ 0) (j : JJ m n r s) :
    StrongDual ℂ (ES m n r s d) := (phiF j.1 j.2).comp (Rt hd)

def eE (j : JJ m n r s) : ES m n r s d := Pt (eF j.1 j.2)

lemma hexpE (hd : ∀ i, d i ≠ 0) (g : ES m n r s d) :
    HasSum (fun j => φE hd j g • eE j) g := by
  have h0 : ∀ f : Sch (NN m n r s), HasSum (fun j : JJ m n r s => phiF j.1 j.2 f • eF j.1 j.2) f :=
    frame_hasSum
  have h1 := tr_exp (E := ES m n r s d) (X := Sch (NN m n r s)) (ι := JJ m n r s)
    (fun j : JJ m n r s => phiF j.1 j.2) (fun j : JJ m n r s => eF j.1 j.2) h0 (Rt hd) Pt (PtRt hd) g
  exact h1

lemma hdomE (hd : ∀ i, d i ≠ 0) : ∀ P : Seminorm ℂ (ES m n r s d), Continuous P →
    ∃ P' : Seminorm ℂ (ES m n r s d), Continuous P' ∧
      ∀ j g, P (eE j) * ‖φE hd j g‖ ≤ cw j * P' g := by
  have h0 : ∀ P : Seminorm ℂ (Sch (NN m n r s)), Continuous P →
      ∃ P' : Seminorm ℂ (Sch (NN m n r s)), Continuous P' ∧
        ∀ (j : JJ m n r s) (f : Sch (NN m n r s)), P (eF j.1 j.2) * ‖phiF j.1 j.2 f‖ ≤ cw j * P' f :=
    frame_dom
  have h1 := tr_dom (E := ES m n r s d) (X := Sch (NN m n r s)) (ι := JJ m n r s)
    (fun j : JJ m n r s => phiF j.1 j.2) (fun j : JJ m n r s => eF j.1 j.2) cw h0 (Rt hd) Pt
  exact h1

lemma es_emb (hd : ∀ i, d i ≠ 0) : IsEmbedding (Rt (m := m) (n := n) (r := r) hd) :=
  Function.LeftInverse.isEmbedding (f := Pt) (PtRt hd) Pt.continuous (Rt hd).continuous

instance esCS : ContinuousSMul ℂ (ES m n r s d) := es_ws.continuousSMul


end

end Aux_ESF



/-!
# Interface: Schwartz–Bruhat spaces that are strict LF-spaces of elementary Schwartz spaces

`SBData G` packages the concrete information about the structural pairs of a group `G` that is
needed to prove that `SchwartzBruhat G` is a strict LF-space of nuclear Fréchet spaces with all
the properties of Lemma 2.1.3.2(1).  The abstract theorem (`Aux_LF.sb_all`) derives the
properties from this data; the concrete instances (adeles, finite adeles, `S`-adeles) only have
to construct the data.

Stages: `X N = range (J N) ⊆ S(G)`, with `J N` the inclusion `S(Γ_N/k_N) → S(G)` attached to a
structural pair `(Γ_N, k_N)` with a presentation `Γ_N/k_N ≅ ℝ^{m N} × ∏_{i < s N} ℤ/d N i`.
`P N : S(G) → S(Γ_N/k_N)` is a projection (`P N ∘ J N = id`) and the projections `p N = J N ∘ P N`
are compatible: `p M ∘ p N = p N = p N ∘ p M` for `N ≤ M`.
-/

set_option autoImplicit false

namespace Aux_LF

open MasulloGRH Topology

/-- the elementary Schwartz space `S(ℝ^m × ∏ ℤ/d_i)` -/
abbrev ESp (m s : ℕ) (d : Fin s → ℕ) : Type := ElemSchwartz m 0 0 s d

structure SBData (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] where
  /-- dimension of the vector part of stage `N` -/
  m : ℕ → ℕ
  /-- number of cyclic factors of the finite part of stage `N` -/
  s : ℕ → ℕ
  /-- orders of the cyclic factors -/
  d : (N : ℕ) → Fin (s N) → ℕ
  hd : ∀ N i, d N i ≠ 0
  /-- the stage inclusions -/
  J : (N : ℕ) → ESp (m N) (s N) (d N) →ₗ[ℂ] SchwartzBruhat G
  /-- the stage projections -/
  P : (N : ℕ) → SchwartzBruhat G →ₗ[ℂ] ESp (m N) (s N) (d N)
  PJ : ∀ N y, P N (J N y) = y
  JP_mono : ∀ N M f, N ≤ M → J M (P M (J N (P N f))) = J N (P N f)
  JP_anti : ∀ N M f, N ≤ M → J N (P N (J M (P M f))) = J N (P N f)
  /-- every Schwartz–Bruhat function lies in some stage -/
  exh : ∀ f, ∃ N, J N (P N f) = f
  /-- each stage inclusion is the inclusion of a structural pair -/
  J_eq : ∀ N, ∃ (Γ k : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup (m N) 0 0 (s N) (d N)))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π),
    ∀ y, J N y = SchwartzBruhat.ofElem Γ k π hs hπ y
  /-- every structural pair lands continuously in some stage -/
  stage : ∀ (Γ k : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (π : Γ →* Multiplicative (ElemGroup m' n' r' s' d')) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π), ∃ M,
      (∀ g, J M (P M (SchwartzBruhat.ofElem Γ k π hs hπ g)) = SchwartzBruhat.ofElem Γ k π hs hπ g) ∧
      Continuous (fun g => P M (SchwartzBruhat.ofElem Γ k π hs hπ g))
  /-- the transition maps between stages are continuous -/
  PJ_cont : ∀ N M, Continuous (fun y => P N (J M y))

end Aux_LF


namespace Aux_ESF

open MasulloGRH Topology Filter Set Aux_SEN Bornology

noncomputable section

variable {m n r s : ℕ} {d : Fin s → ℕ}

/-! ### standalone facts about `S(ℝ^m × 𝕋^n × ℤ^r × F)` -/

lemma es_t2 (hd : ∀ i, d i ≠ 0) : T2Space (ES m n r s d) :=
  (es_emb (m := m) (n := n) (r := r) hd).t2Space

lemma es_complete (hd : ∀ i, d i ≠ 0) :
    @CompleteSpace (ES m n r s d) (IsTopologicalAddGroup.rightUniformSpace _) := by
  letI : UniformSpace (ES m n r s d) := IsTopologicalAddGroup.rightUniformSpace _
  haveI : IsUniformAddGroup (ES m n r s d) := isUniformAddGroup_of_addCommGroup
  refine ⟨fun {f} hf => ?_⟩
  obtain ⟨y, hy⟩ := CompleteSpace.complete (hf.map (Rt hd).uniformContinuous)
  refine ⟨Pt y, ?_⟩
  have e : f = map Pt (map (Rt hd) f) := by
    rw [Filter.map_map]
    have : (Pt ∘ Rt hd : ES m n r s d → ES m n r s d) = id := funext (PtRt hd)
    rw [this, Filter.map_id]
  rw [e]
  exact (Filter.map_mono hy).trans (Pt.continuous.tendsto y)

lemma es_metrizable (hd : ∀ i, d i ≠ 0) : TopologicalSpace.MetrizableSpace (ES m n r s d) :=
  (es_emb (m := m) (n := n) (r := r) hd).metrizableSpace

lemma es_barrelled (hd : ∀ i, d i ≠ 0) : BarrelledSpace ℂ (ES m n r s d) := by
  letI : UniformSpace (ES m n r s d) := IsTopologicalAddGroup.rightUniformSpace _
  haveI : IsUniformAddGroup (ES m n r s d) := isUniformAddGroup_of_addCommGroup
  haveI := es_t2 (m := m) (n := n) (r := r) hd
  haveI := es_metrizable (m := m) (n := n) (r := r) hd
  haveI := es_complete (m := m) (n := n) (r := r) hd
  haveI : (uniformity (ES m n r s d)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  infer_instance

lemma es_dual_complete (hd : ∀ i, d i ≠ 0) :
    @CompleteSpace (StrongDual ℂ (ES m n r s d)) inferInstance := by
  haveI := es_metrizable (m := m) (n := n) (r := r) hd
  infer_instance

end

end Aux_ESF


namespace Aux_LF

open MasulloGRH Topology Filter Set Aux_SEN Aux_ESF Bornology

noncomputable section

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### general facts about the Schwartz–Bruhat topology -/

/-- the inclusion of a structural pair, as a linear map -/
def ofElemL {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : ElemSchwartz m n r s d →ₗ[ℂ] SchwartzBruhat G where
  toFun := SchwartzBruhat.ofElem Γ k π hs hπ
  map_add' f g := by
    apply Subtype.ext
    funext x
    show extendPullback Γ π (f + g).toFun x = extendPullback Γ π f.toFun x + extendPullback Γ π g.toFun x
    unfold extendPullback
    split_ifs
    · rfl
    · simp
  map_smul' c f := by
    apply Subtype.ext
    funext x
    show extendPullback Γ π (c • f).toFun x = c * extendPullback Γ π f.toFun x
    unfold extendPullback
    split_ifs
    · rfl
    · simp

/-- continuity into a space with seminorms (explicit topologies) -/
lemma ccompT {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (tE : TopologicalSpace E) (htg : @IsTopologicalAddGroup E tE _) (tF : TopologicalSpace F)
    {ι : Type*} {q : SeminormFamily ℂ F ι} (hq : WithSeminorms (topology := tF) q) (f : E →ₗ[ℂ] F)
    (hf : ∀ i, @Continuous E ℝ tE _ ((q i).comp f)) : @Continuous E F tE tF f := by
  letI := tE; letI := tF
  exact hq.continuous_of_continuous_comp f hf

lemma tag_of_ws {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} {p : SeminormFamily ℂ E ι}
    (t : TopologicalSpace E) (h : WithSeminorms (topology := t) p) : @IsTopologicalAddGroup E t _ := by
  letI := t; exact h.topologicalAddGroup

lemma cs_of_ws {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} {p : SeminormFamily ℂ E ι}
    (t : TopologicalSpace E) (h : WithSeminorms (topology := t) p) (i : ι) :
    @Continuous E ℝ t _ (p i) := by
  letI := t; exact h.continuous_seminorm i

/-- the seminorms on `S(G)` that are continuous on every structural pair -/
def Qset (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Set (Seminorm ℂ (SchwartzBruhat G)) :=
  {q | ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π), Continuous (fun g => q (SchwartzBruhat.ofElem Γ k π hs hπ g))}

def qfam (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :
    SeminormFamily ℂ (SchwartzBruhat G) (Qset G) := fun q => q.1

lemma zero_mem_Qset : (0 : Seminorm ℂ (SchwartzBruhat G)) ∈ Qset G := by
  intro Γ k m n r s d π hs hπ
  simp only [Seminorm.zero_apply]
  exact continuous_const

lemma ofElem_cont {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) :=
  continuous_sInf_rng.2 fun _ ht => ht.2 Γ k m n r s d π hs hπ

/-- the topology of the seminorms in `Qset` -/
def tQ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :
    TopologicalSpace (SchwartzBruhat G) := (qfam G).moduleFilterBasis.topology

theorem sb_ws : WithSeminorms (qfam G) := by
  have hws : WithSeminorms (topology := tQ G) (qfam G) :=
    WithSeminorms.mk (topology := tQ G) (p := qfam G) rfl
  have hTG := tag_of_ws (tQ G) hws
  refine ⟨le_antisymm ?_ ?_⟩
  · -- the `Q`-topology belongs to the defining family
    refine sInf_le ⟨⟨Qset G, ⟨⟨0, zero_mem_Qset⟩⟩, qfam G, hws⟩, ?_⟩
    intro Γ k m n r s d π hs hπ
    exact ccompT _ inferInstance (tQ G) hws (ofElemL Γ k π hs hπ) fun q => q.2 Γ k m n r s d π hs hπ
  · refine le_sInf fun t ht => ?_
    obtain ⟨⟨ι, _, p, hp⟩, hcont⟩ := ht
    have hmem : ∀ i, p i ∈ Qset G := fun i Γ k m n r s d π hs hπ =>
      (cs_of_ws t hp i).comp (hcont Γ k m n r s d π hs hπ)
    have : @Continuous _ _ (tQ G) t (LinearMap.id : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G) :=
      ccompT (tQ G) hTG t hp LinearMap.id fun i => cs_of_ws (tQ G) hws ⟨p i, hmem i⟩
    exact continuous_id_iff_le.1 this

instance sbTG : IsTopologicalAddGroup (SchwartzBruhat G) := (sb_ws (G := G)).topologicalAddGroup

instance sbCS : ContinuousSMul ℂ (SchwartzBruhat G) := (sb_ws (G := G)).continuousSMul

lemma sb_cont_of (q : Seminorm ℂ (SchwartzBruhat G)) (hq : q ∈ Qset G) : Continuous q :=
  (sb_ws (G := G)).continuous_seminorm ⟨q, hq⟩

lemma sb_lc : IsLocallyConvexTopology (SchwartzBruhat G) inferInstance := lc_of_ws (sb_ws (G := G))

instance sbBarrelled : BarrelledSpace ℂ (SchwartzBruhat G) := by
  refine ⟨fun q hq => sb_cont_of q fun Γ k m n r s d π hs hπ => ?_⟩
  haveI := es_barrelled (m := m) (n := n) (r := r) hπ.1
  have h1 : LowerSemicontinuous (q.comp (ofElemL Γ k π hs hπ)) :=
    hq.comp (ofElem_cont Γ k π hs hπ)
  exact BarrelledSpace.continuous_of_lowerSemicontinuous _ h1

/-! ### seminorms given by finite sums -/

section fsum

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- `f ↦ ∑_N w_N σ_N(f)` for seminorms that vanish beyond a level depending on `f` -/
def fsum (σ : ℕ → Seminorm ℂ E) (w : ℕ → ℝ) (hw : ∀ N, 0 ≤ w N)
    (hfin : ∀ f, ∃ M, ∀ N, M < N → σ N f = 0) : Seminorm ℂ E where
  toFun f := ∑' N, w N * σ N f
  map_zero' := by simp
  add_le' f g := by
    obtain ⟨M1, h1⟩ := hfin f
    obtain ⟨M2, h2⟩ := hfin g
    obtain ⟨M3, h3⟩ := hfin (f + g)
    set K := max M1 (max M2 M3)
    have e : ∀ x : E, (∀ N, K < N → σ N x = 0) →
        ∑' N, w N * σ N x = ∑ N ∈ Finset.range (K + 1), w N * σ N x := fun x hx =>
      tsum_eq_sum fun N hN => by
        rw [Finset.mem_range, not_lt] at hN
        rw [hx N (by omega), mul_zero]
    rw [e f fun N hN => h1 N (by omega), e g fun N hN => h2 N (by omega),
      e (f + g) fun N hN => h3 N (by omega), ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun N _ => by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (map_add_le_add _ _ _) (hw N)
  neg' f := by simp
  smul' c f := by
    simp only [map_smul_eq_mul, ← tsum_mul_left]
    congr 1; funext N; ring

lemma fsum_apply (σ : ℕ → Seminorm ℂ E) (w : ℕ → ℝ) (hw : ∀ N, 0 ≤ w N)
    (hfin : ∀ f, ∃ M, ∀ N, M < N → σ N f = 0) (f : E) (K : ℕ) (hK : ∀ N, K < N → σ N f = 0) :
    fsum σ w hw hfin f = ∑ N ∈ Finset.range (K + 1), w N * σ N f :=
  tsum_eq_sum fun N hN => by
    rw [Finset.mem_range, not_lt] at hN
    rw [hK N (by omega), mul_zero]

lemma le_fsum (σ : ℕ → Seminorm ℂ E) (w : ℕ → ℝ) (hw : ∀ N, 0 ≤ w N)
    (hfin : ∀ f, ∃ M, ∀ N, M < N → σ N f = 0) (f : E) (N : ℕ) :
    w N * σ N f ≤ fsum σ w hw hfin f := by
  obtain ⟨M, hM⟩ := hfin f
  rw [fsum_apply σ w hw hfin f (max M N) fun N' hN' => hM N' (by omega)]
  exact Finset.single_le_sum (f := fun N => w N * σ N f)
    (fun N _ => mul_nonneg (hw N) (apply_nonneg _ _)) (Finset.mem_range.2 (by omega))

end fsum

/-! ### the stage structure -/

section stages

variable (D : SBData G)

lemma J_cont (N : ℕ) : Continuous (D.J N) := by
  obtain ⟨Γ, k, π, hs, hπ, h⟩ := D.J_eq N
  have : (D.J N : ESp (D.m N) (D.s N) (D.d N) → SchwartzBruhat G) =
      SchwartzBruhat.ofElem Γ k π hs hπ := funext h
  rw [this]; exact ofElem_cont Γ k π hs hπ

lemma univ (q : Seminorm ℂ (SchwartzBruhat G)) (hq : ∀ N, Continuous fun y => q (D.J N y)) :
    Continuous q := by
  refine sb_cont_of q fun Γ k m n r s d π hs hπ => ?_
  obtain ⟨M, h1, h2⟩ := D.stage Γ k m n r s d π hs hπ
  have : (fun g => q (SchwartzBruhat.ofElem Γ k π hs hπ g)) =
      (fun y => q (D.J M y)) ∘ (fun g => D.P M (SchwartzBruhat.ofElem Γ k π hs hπ g)) := by
    funext g; simp only [Function.comp_apply, h1]
  rw [this]; exact (hq M).comp h2

lemma lin_cont {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] {κ : Type*}
    {pY : SeminormFamily ℂ Y κ} (hY : WithSeminorms pY) (T : SchwartzBruhat G →ₗ[ℂ] Y)
    (hT : ∀ N, Continuous fun y => T (D.J N y)) : Continuous T :=
  hY.continuous_of_continuous_comp T fun i =>
    univ D _ fun N => (hY.continuous_seminorm i).comp (hT N)

lemma P_cont (N : ℕ) : Continuous (D.P N) :=
  lin_cont D es_ws (D.P N) fun M => D.PJ_cont N M

/-- the projection onto stage `N` -/
def pl (N : ℕ) : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G := (D.J N).comp (D.P N)

lemma pl_apply (N : ℕ) (f : SchwartzBruhat G) : pl D N f = D.J N (D.P N f) := rfl

lemma pl_cont (N : ℕ) : Continuous (pl D N) := (J_cont D N).comp (P_cont D N)

/-- the level-`N` part -/
def dl : ℕ → SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G
  | 0 => pl D 0
  | N + 1 => pl D (N + 1) - pl D N

lemma dl_cont (N : ℕ) : Continuous (dl D N) := by
  cases N with
  | zero => exact pl_cont D 0
  | succ N => exact (pl_cont D (N + 1)).sub (pl_cont D N)

lemma pl_of_le {f : SchwartzBruhat G} {M N : ℕ} (hf : pl D M f = f) (h : M ≤ N) :
    pl D N f = f := by
  rw [← hf]
  exact D.JP_mono M N f h

lemma pl_pl_le {f : SchwartzBruhat G} {M N : ℕ} (h : M ≤ N) : pl D N (pl D M f) = pl D M f :=
  D.JP_mono M N f h

lemma pl_pl_ge {f : SchwartzBruhat G} {M N : ℕ} (h : N ≤ M) : pl D N (pl D M f) = pl D N f :=
  D.JP_anti N M f h

lemma dl_zero_of_lt {f : SchwartzBruhat G} {M N : ℕ} (hf : pl D M f = f) (h : M < N) :
    dl D N f = 0 := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  show pl D (N' + 1) f - pl D N' f = 0
  rw [pl_of_le D hf (by omega), pl_of_le D hf (by omega), sub_self]

lemma sum_dl (f : SchwartzBruhat G) (K : ℕ) :
    ∑ N ∈ Finset.range (K + 1), dl D N f = pl D K f := by
  induction K with
  | zero => simp [dl]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    show pl D K f + (pl D (K + 1) f - pl D K f) = _
    abel

lemma level (f : SchwartzBruhat G) : ∃ M, pl D M f = f := D.exh f

lemma eq_sum_dl {f : SchwartzBruhat G} {M : ℕ} (hf : pl D M f = f) :
    ∑ N ∈ Finset.range (M + 1), dl D N f = f := by rw [sum_dl, hf]

lemma pl_dl (N : ℕ) (f : SchwartzBruhat G) : pl D N (dl D N f) = dl D N f := by
  cases N with
  | zero =>
    show pl D 0 (pl D 0 f) = pl D 0 f
    exact pl_pl_le D le_rfl
  | succ N =>
    show pl D (N + 1) (pl D (N + 1) f - pl D N f) = pl D (N + 1) f - pl D N f
    rw [map_sub, pl_pl_le D le_rfl, pl_pl_le D (by omega)]

lemma pl_J (N : ℕ) (y : ESp (D.m N) (D.s N) (D.d N)) : pl D N (D.J N y) = D.J N y := by
  rw [pl_apply, D.PJ]

lemma dl_fin (f : SchwartzBruhat G) : ∃ M, ∀ N, M < N → dl D N f = 0 := by
  obtain ⟨M, hM⟩ := level D f
  exact ⟨M, fun N hN => dl_zero_of_lt D hM hN⟩

/-- seminorms built from the level parts -/
def lsum (ρ : (N : ℕ) → Seminorm ℂ (ESp (D.m N) (D.s N) (D.d N))) (w : ℕ → ℝ)
    (hw : ∀ N, 0 ≤ w N) : Seminorm ℂ (SchwartzBruhat G) :=
  fsum (fun N => (ρ N).comp ((D.P N).comp (dl D N))) w hw fun f => by
    obtain ⟨M, hM⟩ := dl_fin D f
    exact ⟨M, fun N hN => by simp [hM N hN]⟩

lemma lsum_apply (ρ : (N : ℕ) → Seminorm ℂ (ESp (D.m N) (D.s N) (D.d N))) (w : ℕ → ℝ)
    (hw : ∀ N, 0 ≤ w N) (f : SchwartzBruhat G) {K : ℕ} (hK : pl D K f = f) :
    lsum D ρ w hw f = ∑ N ∈ Finset.range (K + 1), w N * ρ N (D.P N (dl D N f)) := by
  rw [lsum, fsum_apply _ w hw _ f K fun N hN => by
    simp [dl_zero_of_lt D hK hN]]
  rfl

lemma le_lsum (ρ : (N : ℕ) → Seminorm ℂ (ESp (D.m N) (D.s N) (D.d N))) (w : ℕ → ℝ)
    (hw : ∀ N, 0 ≤ w N) (f : SchwartzBruhat G) (N : ℕ) :
    w N * ρ N (D.P N (dl D N f)) ≤ lsum D ρ w hw f :=
  le_fsum (fun N => (ρ N).comp ((D.P N).comp (dl D N))) w hw _ f N

lemma lsum_cont (ρ : (N : ℕ) → Seminorm ℂ (ESp (D.m N) (D.s N) (D.d N))) (w : ℕ → ℝ)
    (hw : ∀ N, 0 ≤ w N) (hρ : ∀ N, Continuous (ρ N)) : Continuous (lsum D ρ w hw) := by
  refine univ D _ fun K => ?_
  have e : (fun y => lsum D ρ w hw (D.J K y)) = fun y =>
      ∑ N ∈ Finset.range (K + 1), w N * ρ N (D.P N (dl D N (D.J K y))) := by
    funext y; exact lsum_apply D ρ w hw _ (pl_J D K y)
  rw [e]
  refine continuous_finsetSum _ fun N _ => continuous_const.mul ((hρ N).comp ?_)
  exact (P_cont D N).comp ((dl_cont D N).comp (J_cont D K))

/-- Hausdorff -/
lemma sb_t2 (D : SBData G) : T2Space (SchwartzBruhat G) := by
  have : T1Space (SchwartzBruhat G) := WithSeminorms.T1_of_separating (sb_ws (G := G)) fun f hf => by
    obtain ⟨M, hM⟩ := level D f
    have : ∃ N, D.P N (dl D N f) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hf
      rw [← eq_sum_dl D hM]
      refine Finset.sum_eq_zero fun N _ => ?_
      rw [← pl_dl D N f, pl_apply, h N, map_zero]
    obtain ⟨N, hN⟩ := this
    haveI := es_t2 (m := D.m N) (n := 0) (r := 0) (D.hd N)
    obtain ⟨p, hp⟩ := WithSeminorms.separating_of_T1 es_ws _ hN
    let q : Seminorm ℂ (SchwartzBruhat G) := (sn p).comp ((D.P N).comp (dl D N))
    have hq : q ∈ Qset G := fun Γ k m n r s d π hs hπ =>
      ((es_ws.continuous_seminorm p).comp ((P_cont D N).comp (dl_cont D N))).comp
        (ofElem_cont Γ k π hs hπ)
    exact ⟨⟨q, hq⟩, hp⟩
  infer_instance

end stages

end

end Aux_LF


namespace Aux_LF

open MasulloGRH Topology Filter Set Aux_SEN Aux_ESF Bornology

noncomputable section

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### algebra of the level parts -/

section alg

variable (D : SBData G)

lemma pl_pl (a b : ℕ) (f : SchwartzBruhat G) : pl D a (pl D b f) = pl D (min a b) f := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; exact pl_pl_ge D h
  · rw [min_eq_right h]; exact pl_pl_le D h

lemma pl_dl' (a b : ℕ) (f : SchwartzBruhat G) :
    pl D a (dl D b f) = if b ≤ a then dl D b f else 0 := by
  cases b with
  | zero =>
    show pl D a (pl D 0 f) = if 0 ≤ a then pl D 0 f else 0
    rw [if_pos (Nat.zero_le a), pl_pl, min_eq_right (Nat.zero_le a)]
  | succ b =>
    show pl D a (pl D (b + 1) f - pl D b f) = if b + 1 ≤ a then pl D (b + 1) f - pl D b f else 0
    rw [map_sub, pl_pl, pl_pl]
    split_ifs with h
    · rw [min_eq_right h, min_eq_right (by omega)]
    · rw [min_eq_left (by omega), min_eq_left (by omega), sub_self]

lemma dl_dl (a b : ℕ) (f : SchwartzBruhat G) :
    dl D a (dl D b f) = if a = b then dl D b f else 0 := by
  cases a with
  | zero =>
    show pl D 0 (dl D b f) = _
    rw [pl_dl']
    split_ifs <;> first | rfl | omega
  | succ a =>
    show pl D (a + 1) (dl D b f) - pl D a (dl D b f) = _
    rw [pl_dl', pl_dl']
    split_ifs <;> first | (exfalso; omega) | simp

lemma J_P_dl (N : ℕ) (f : SchwartzBruhat G) : D.J N (D.P N (dl D N f)) = dl D N f := pl_dl D N f

end alg

/-! ### the frame of `S(G)` -/

section frame

variable (D : SBData G)

abbrev Idx (D : SBData G) := Σ N : ℕ, JJ (D.m N) 0 0 (D.s N)

def SN (N : ℕ) : ℝ := ∑' j : JJ (D.m N) 0 0 (D.s N), cw j

lemma SN_nonneg (N : ℕ) : 0 ≤ SN D N := tsum_nonneg fun j => (cw_pos j).le

def PdlL (N : ℕ) : SchwartzBruhat G →L[ℂ] ESp (D.m N) (D.s N) (D.d N) :=
  ⟨(D.P N).comp (dl D N), (P_cont D N).comp (dl_cont D N)⟩

lemma PdlL_apply (N : ℕ) (f : SchwartzBruhat G) : PdlL D N f = D.P N (dl D N f) := rfl

def Phi (i : Idx D) : StrongDual ℂ (SchwartzBruhat G) :=
  (φE (D.hd i.1) i.2).comp (PdlL D i.1)

def Evec (i : Idx D) : SchwartzBruhat G := D.J i.1 (eE i.2)

def Cw (i : Idx D) : ℝ := cw i.2 / (2 ^ i.1 * (SN D i.1 + 1))

lemma Cw_pos (i : Idx D) : 0 < Cw D i := by
  have := SN_nonneg D i.1
  have := cw_pos i.2
  unfold Cw; positivity

lemma Cw_summable : Summable (Cw D) := by
  refine (summable_sigma_of_nonneg fun i => (Cw_pos D i).le).2 ⟨fun N => ?_, ?_⟩
  · have h : Summable (fun j : JJ (D.m N) 0 0 (D.s N) => cw j / (2 ^ N * (SN D N + 1))) :=
      (cw_summable).div_const _
    exact h
  · refine Summable.of_nonneg_of_le (fun N => tsum_nonneg fun j => (Cw_pos D ⟨N, j⟩).le)
      (fun N => ?_) (summable_geometric_two)
    show ∑' j, cw j / (2 ^ N * (SN D N + 1)) ≤ (1 / 2) ^ N
    rw [tsum_div_const]
    have h0 := SN_nonneg D N
    rw [div_le_iff₀ (by positivity)]
    show SN D N ≤ (1 / 2) ^ N * (2 ^ N * (SN D N + 1))
    rw [← mul_assoc, ← mul_pow, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_pow, one_mul]
    linarith

lemma frame_exp (f : SchwartzBruhat G) : HasSum (fun i => Phi D i f • Evec D i) f := by
  classical
  obtain ⟨M, hM⟩ := level D f
  let F : Idx D → SchwartzBruhat G := fun i => Phi D i f • Evec D i
  let FN : ℕ → Idx D → SchwartzBruhat G := fun N i => if i.1 = N then F i else 0
  have hF : F = fun i => ∑ N ∈ Finset.range (M + 1), FN N i := by
    funext i
    show F i = ∑ N ∈ Finset.range (M + 1), (if i.1 = N then F i else 0)
    rw [Finset.sum_ite_eq]
    by_cases hi : i.1 ≤ M
    · rw [if_pos (Finset.mem_range.2 (by omega))]
    · have h0 : dl D i.1 f = 0 := dl_zero_of_lt D hM (by omega)
      have : F i = 0 := by
        show Phi D i f • Evec D i = 0
        rw [Phi, ContinuousLinearMap.comp_apply, PdlL_apply, h0, map_zero, map_zero, zero_smul]
      rw [this, if_neg (by rw [Finset.mem_range]; omega)]
  have hN : ∀ N, HasSum (FN N) (dl D N f) := by
    intro N
    let g : JJ (D.m N) 0 0 (D.s N) → Idx D := fun j => ⟨N, j⟩
    have hg : Function.Injective g := fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2
    have hv : ∀ i ∉ Set.range g, FN N i = 0 := by
      rintro ⟨N', j⟩ hi
      have : N' ≠ N := by rintro rfl; exact hi ⟨j, rfl⟩
      show (if N' = N then F ⟨N', j⟩ else 0) = 0
      rw [if_neg this]
    rw [← hg.hasSum_iff hv]
    have e : FN N ∘ g = fun j => D.J N (φE (D.hd N) j (D.P N (dl D N f)) • eE j) := by
      funext j
      show (if N = N then F ⟨N, j⟩ else 0) = _
      rw [if_pos rfl, map_smul]
      rfl
    rw [e]
    have h := (hexpE (D.hd N) (D.P N (dl D N f))).map (D.J N) (J_cont D N)
    rw [J_P_dl D N f] at h
    exact h
  rw [show (fun i => Phi D i f • Evec D i) = F from rfl, hF]
  have := hasSum_sum (s := Finset.range (M + 1)) fun N _ => hN N
  rwa [eq_sum_dl D hM] at this

lemma frame_dom (Pn : Seminorm ℂ (SchwartzBruhat G)) (hPn : Continuous Pn) :
    ∃ P' : Seminorm ℂ (SchwartzBruhat G), Continuous P' ∧
      ∀ i f, Pn (Evec D i) * ‖Phi D i f‖ ≤ Cw D i * P' f := by
  have h : ∀ N, ∃ ρ : Seminorm ℂ (ESp (D.m N) (D.s N) (D.d N)), Continuous ρ ∧
      ∀ j y, (Pn.comp (D.J N)) (eE j) * ‖φE (D.hd N) j y‖ ≤ cw j * ρ y := fun N =>
    hdomE (D.hd N) (Pn.comp (D.J N)) (hPn.comp (J_cont D N))
  choose ρ hρc hρ using h
  have hw : ∀ N, 0 ≤ 2 ^ N * (SN D N + 1) := fun N => by have := SN_nonneg D N; positivity
  refine ⟨lsum D ρ (fun N => 2 ^ N * (SN D N + 1)) hw, lsum_cont D ρ _ hw hρc, fun i f => ?_⟩
  obtain ⟨N, j⟩ := i
  have h1 := hρ N j (D.P N (dl D N f))
  have h2 := le_lsum D ρ (fun N => 2 ^ N * (SN D N + 1)) hw f N
  have hpos : 0 < 2 ^ N * (SN D N + 1) := by have := SN_nonneg D N; positivity
  have e : cw j = Cw D ⟨N, j⟩ * (2 ^ N * (SN D N + 1)) := by
    show cw j = cw j / (2 ^ N * (SN D N + 1)) * (2 ^ N * (SN D N + 1))
    rw [div_mul_cancel₀ _ hpos.ne']
  calc Pn (Evec D ⟨N, j⟩) * ‖Phi D ⟨N, j⟩ f‖ ≤ cw j * ρ N (D.P N (dl D N f)) := h1
    _ = Cw D ⟨N, j⟩ * (2 ^ N * (SN D N + 1) * ρ N (D.P N (dl D N f))) := by rw [e]; ring
    _ ≤ Cw D ⟨N, j⟩ * lsum D ρ (fun N => 2 ^ N * (SN D N + 1)) hw f :=
        mul_le_mul_of_nonneg_left h2 (Cw_pos D _).le

end frame

/-! ### completeness -/

section complete

variable (D : SBData G)

lemma es_lim {m s : ℕ} {d : Fin s → ℕ} (hd : ∀ i, d i ≠ 0) (𝒢 : Filter (ESp m s d)) [𝒢.NeBot]
    (h : ∀ U ∈ 𝓝 (0 : ESp m s d), ∃ A ∈ 𝒢, ∀ x ∈ A, ∀ y ∈ A, x - y ∈ U) :
    ∃ z, 𝒢 ≤ 𝓝 z := by
  letI : UniformSpace (ESp m s d) := IsTopologicalAddGroup.rightUniformSpace _
  haveI : IsUniformAddGroup (ESp m s d) := isUniformAddGroup_of_addCommGroup
  haveI := es_complete (m := m) (n := 0) (r := 0) hd
  refine CompleteSpace.complete ⟨inferInstance, fun V hV => ?_⟩
  rw [uniformity_eq_comap_nhds_zero] at hV
  obtain ⟨U, hU, hUV⟩ := hV
  obtain ⟨A, hA, hAU⟩ := h U hU
  refine Filter.mem_of_superset (prod_mem_prod hA hA) fun p hp => hUV ?_
  exact hAU p.2 hp.2 p.1 hp.1

theorem sb_ctvs (D : SBData G) : IsCompleteTVS (SchwartzBruhat G) := by
  classical
  haveI := sb_t2 D
  refine ⟨inferInstance, fun 𝒻 h𝒻 => ?_⟩
  obtain ⟨hne, hc⟩ := h𝒻
  -- the level parts converge
  have hlim : ∀ N, ∃ z, map (PdlL D N) 𝒻 ≤ 𝓝 z := by
    intro N
    refine es_lim (D.hd N) _ fun U hU => ?_
    obtain ⟨A, hA, hAU⟩ := hc _ ((PdlL D N).continuous.tendsto 0 (by rw [map_zero]; exact hU))
    refine ⟨PdlL D N '' A, image_mem_map hA, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_sub]; exact hAU x hx y hy
  choose z hz using hlim
  -- the limits are level parts
  have hzl : ∀ N N', dl D N' (D.J N (z N)) = if N' = N then D.J N (z N) else 0 := by
    intro N N'
    have t1 : Tendsto (fun f => dl D N' (D.J N (PdlL D N f))) 𝒻 (𝓝 (dl D N' (D.J N (z N)))) :=
      ((dl_cont D N').comp (J_cont D N)).continuousAt.tendsto.comp (hz N)
    have t2 : Tendsto (fun f => dl D N' (D.J N (PdlL D N f))) 𝒻
        (𝓝 (if N' = N then D.J N (z N) else 0)) := by
      have e : (fun f => dl D N' (D.J N (PdlL D N f))) =
          fun f => if N' = N then D.J N (PdlL D N f) else 0 := by
        funext f
        rw [PdlL_apply, J_P_dl, dl_dl, ← J_P_dl D N f]
      rw [e]
      split_ifs
      · exact (J_cont D N).continuousAt.tendsto.comp (hz N)
      · exact tendsto_const_nhds
    exact tendsto_nhds_unique t1 t2
  -- only finitely many levels survive
  have hfin : ∃ M, ∀ N, M < N → z N = 0 := by
    by_contra hcon
    push_neg at hcon
    have hsep : ∀ N, ∃ ρ : Seminorm ℂ (ESp (D.m N) (D.s N) (D.d N)), Continuous ρ ∧
        (z N ≠ 0 → 0 < ρ (z N)) := by
      intro N
      by_cases h0 : z N = 0
      · exact ⟨0, continuous_const, fun h => (h h0).elim⟩
      · haveI := es_t2 (m := D.m N) (n := 0) (r := 0) (D.hd N)
        obtain ⟨p, hp⟩ := WithSeminorms.separating_of_T1 es_ws _ h0
        exact ⟨sn p, es_ws.continuous_seminorm p, fun _ => lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hp)⟩
    choose ρ hρc hρ using hsep
    let w : ℕ → ℝ := fun N => if z N = 0 then 0 else 2 / ρ N (z N)
    have hw : ∀ N, 0 ≤ w N := fun N => by
      show 0 ≤ (if z N = 0 then 0 else 2 / ρ N (z N))
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg zero_le_two (hρ N h).le
    let Q := lsum D ρ w hw
    have hQ : {x | Q x < 1} ∈ 𝓝 (0 : SchwartzBruhat G) :=
      (lsum_cont D ρ w hw hρc).continuousAt.preimage_mem_nhds (by
        rw [map_zero]; exact Iio_mem_nhds one_pos)
    obtain ⟨A, hA, hAQ⟩ := hc _ hQ
    obtain ⟨a, ha⟩ := hne.nonempty_of_mem hA
    obtain ⟨M0, hM0⟩ := level D a
    obtain ⟨N, hN, hzN⟩ := hcon M0
    have hdl0 : dl D N a = 0 := dl_zero_of_lt D hM0 hN
    have hC : IsClosed {y : ESp (D.m N) (D.s N) (D.d N) | w N * ρ N y ≤ 1} :=
      isClosed_le (continuous_const.mul (hρc N)) continuous_const
    have hev : ∀ᶠ b in 𝒻, PdlL D N b ∈ {y | w N * ρ N y ≤ 1} := by
      filter_upwards [hA] with b hb
      have h1 := hAQ b hb a ha
      have h2 := le_lsum D ρ w hw (b - a) N
      show w N * ρ N (D.P N (dl D N b)) ≤ 1
      rw [map_sub, hdl0, map_sub, map_zero, sub_zero] at h2
      exact h2.trans (le_of_lt h1)
    have hmem := hC.mem_of_tendsto (hz N) hev
    simp only [Set.mem_ofPred_eq, w, if_neg hzN] at hmem
    have hpos := hρ N hzN
    rw [div_mul_cancel₀ _ hpos.ne'] at hmem
    norm_num at hmem
  obtain ⟨M, hM⟩ := hfin
  let g : SchwartzBruhat G := ∑ N ∈ Finset.range (M + 1), D.J N (z N)
  refine ⟨g, ?_⟩
  -- level parts of `g`
  have hPg : ∀ N, D.P N (dl D N g) = z N := by
    intro N
    have : dl D N g = D.J N (z N) := by
      simp only [g, map_sum, hzl]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · rw [hM N (by rw [Finset.mem_range] at h; omega), map_zero]
    rw [this, D.PJ]
  have hgl : pl D M g = g := by
    simp only [g, map_sum]
    exact Finset.sum_congr rfl fun N hN => pl_of_le D (pl_J D N (z N))
      (by rw [Finset.mem_range] at hN; omega)
  show Tendsto id 𝒻 (𝓝 g)
  rw [(sb_ws (G := G)).tendsto_nhds]
  rintro ⟨q, hq⟩ ε hε
  have hqc : Continuous q := sb_cont_of q hq
  let ρ : (N : ℕ) → Seminorm ℂ (ESp (D.m N) (D.s N) (D.d N)) := fun N => q.comp (D.J N)
  have hρc : ∀ N, Continuous (ρ N) := fun N => hqc.comp (J_cont D N)
  let Q' := lsum D ρ (fun _ => 1) (fun _ => zero_le_one)
  have hQ' : {x | Q' x < ε / 2} ∈ 𝓝 (0 : SchwartzBruhat G) :=
    (lsum_cont D ρ _ _ hρc).continuousAt.preimage_mem_nhds (by
      rw [map_zero]; exact Iio_mem_nhds (half_pos hε))
  obtain ⟨A, hA, hAQ⟩ := hc _ hQ'
  filter_upwards [hA] with a ha
  obtain ⟨La, hLa⟩ := level D a
  set K := max La M
  have hK : pl D K (a - g) = a - g := by
    rw [map_sub, pl_of_le D hLa (le_max_left _ _), pl_of_le D hgl (le_max_right _ _)]
  -- `q (a - g)` is bounded by the level sums
  have h1 : q (id a - g) ≤ ∑ N ∈ Finset.range (K + 1), q (D.J N (D.P N (dl D N a) - z N)) := by
    have e : id a - g = ∑ N ∈ Finset.range (K + 1), D.J N (D.P N (dl D N a) - z N) := by
      show a - g = _
      rw [← eq_sum_dl D hK]
      refine Finset.sum_congr rfl fun N _ => ?_
      rw [← J_P_dl D N (a - g), map_sub (dl D N), map_sub (D.P N), hPg]
    rw [e]
    exact Finset.le_sum_of_subadditive (⇑q) (map_zero _).le (map_add_le_add _) _ _
  have h2 : ∑ N ∈ Finset.range (K + 1), q (D.J N (D.P N (dl D N a) - z N)) ≤ ε / 2 := by
    have t : Tendsto (fun b => ∑ N ∈ Finset.range (K + 1),
        q (D.J N (D.P N (dl D N a) - PdlL D N b))) 𝒻
        (𝓝 (∑ N ∈ Finset.range (K + 1), q (D.J N (D.P N (dl D N a) - z N)))) := by
      refine tendsto_finsetSum _ fun N _ => ?_
      have hc' : Continuous fun y => q (D.J N (D.P N (dl D N a) - y)) :=
        hqc.comp ((J_cont D N).comp (continuous_const.sub continuous_id))
      exact hc'.continuousAt.tendsto.comp (hz N)
    refine le_of_tendsto t ?_
    filter_upwards [hA] with b hb
    obtain ⟨Lb, hLb⟩ := level D b
    have hab : pl D (max K Lb) (a - b) = a - b := by
      rw [map_sub, pl_of_le D hLa (by omega), pl_of_le D hLb (le_max_right _ _)]
    have h3 := lsum_apply D ρ (fun _ => 1) (fun _ => zero_le_one) (a - b) hab
    have h4 : ∑ N ∈ Finset.range (K + 1), q (D.J N (D.P N (dl D N a) - PdlL D N b)) ≤
        ∑ N ∈ Finset.range (max K Lb + 1), 1 * ρ N (D.P N (dl D N (a - b))) := by
      refine (Finset.sum_le_sum fun N _ => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (by omega)) fun N _ _ => by positivity)
      rw [one_mul, PdlL_apply, map_sub (dl D N), map_sub (D.P N)]
      exact le_rfl
    have h5 := hAQ a ha b hb
    simp only [Set.mem_ofPred_eq] at h5
    rw [← h3] at h4
    exact h4.trans h5.le
  exact lt_of_le_of_lt (h1.trans h2) (half_lt_self hε)

instance sbU : UniformSpace (SchwartzBruhat G) := IsTopologicalAddGroup.rightUniformSpace _

instance sbUG : IsUniformAddGroup (SchwartzBruhat G) := isUniformAddGroup_of_addCommGroup

lemma cs_of_ctvs {E : Type*} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
    (h : IsCompleteTVS E) : CompleteSpace E := by
  refine ⟨fun {f} hf => h.2 f ⟨hf.1, fun U hU => ?_⟩⟩
  have : {p : E × E | p.2 - p.1 ∈ U} ∈ uniformity E := by
    rw [uniformity_eq_comap_nhds_zero]; exact preimage_mem_comap hU
  obtain ⟨A, hA, hAU⟩ := mem_prod_same_iff.1 (hf.2 this)
  exact ⟨A, hA, fun x hx y hy => hAU (mk_mem_prod hy hx)⟩

lemma sb_complete (D : SBData G) : CompleteSpace (SchwartzBruhat G) := cs_of_ctvs (sb_ctvs D)

end complete

end

end Aux_LF


namespace Aux_LF

open MasulloGRH Topology Filter Set Aux_SEN Aux_ESF Bornology

noncomputable section

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### all continuous seminorms -/

lemma ws_all {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    WithSeminorms (fun q : {q : Seminorm ℂ E // Continuous q} => q.1) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun q => ?_) ?_
  · rw [← tendsto_iff_comap]
    have := q.2.tendsto 0
    rwa [map_zero] at this
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf p).1 hp]
    exact le_iInf fun i => iInf_le_of_le ⟨p i, hp.continuous_seminorm i⟩ le_rfl

/-! ### the strong dual is complete -/

section dual

variable (D : SBData G)

def JL (N : ℕ) : ESp (D.m N) (D.s N) (D.d N) →L[ℂ] SchwartzBruhat G := ⟨D.J N, J_cont D N⟩

theorem dual_complete (D : SBData G) : CompleteSpace (StrongDual ℂ (SchwartzBruhat G)) := by
  refine ⟨fun {𝒢} h𝒢 => ?_⟩
  haveI := h𝒢.1
  -- pointwise limits
  have hpt : ∀ x : SchwartzBruhat G, ∃ c : ℂ,
      Tendsto (fun T : StrongDual ℂ (SchwartzBruhat G) => T x) 𝒢 (𝓝 c) :=
    fun x => CompleteSpace.complete (h𝒢.map (evl x).uniformContinuous)
  choose T0 hT0 using hpt
  have hadd : ∀ x y, T0 (x + y) = T0 x + T0 y := fun x y => by
    have t1 : Tendsto (fun T : StrongDual ℂ (SchwartzBruhat G) => T (x + y)) 𝒢 (𝓝 (T0 x + T0 y)) := by
      have := (hT0 x).add (hT0 y)
      convert this using 2 with T
      exact map_add T x y
    exact tendsto_nhds_unique (hT0 (x + y)) t1
  have hsmul : ∀ (c : ℂ) x, T0 (c • x) = c • T0 x := fun c x => by
    have t1 : Tendsto (fun T : StrongDual ℂ (SchwartzBruhat G) => T (c • x)) 𝒢 (𝓝 (c • T0 x)) := by
      have := (hT0 x).const_mul c
      rw [smul_eq_mul]
      convert this using 2 with T
      rw [map_smul, smul_eq_mul]
    exact tendsto_nhds_unique (hT0 (c • x)) t1
  let TL : SchwartzBruhat G →ₗ[ℂ] ℂ := ⟨⟨T0, hadd⟩, hsmul⟩
  have hTc : Continuous TL := by
    refine lin_cont D (norm_withSeminorms ℂ ℂ) TL fun N => ?_
    letI : UniformSpace (StrongDual ℂ (ESp (D.m N) (D.s N) (D.d N))) := inferInstance
    haveI := es_dual_complete (m := D.m N) (n := 0) (r := 0) (D.hd N)
    let Pre : StrongDual ℂ (SchwartzBruhat G) →L[ℂ] StrongDual ℂ (ESp (D.m N) (D.s N) (D.d N)) :=
      ContinuousLinearMap.precomp ℂ (JL D N)
    obtain ⟨S, hS⟩ := CompleteSpace.complete (h𝒢.map Pre.uniformContinuous)
    have e : (fun y => TL (D.J N y)) = S := by
      funext y
      have t1 : Tendsto (fun T : StrongDual ℂ (SchwartzBruhat G) => (Pre T) y) 𝒢 (𝓝 (S y)) :=
        ((evl y).continuous.tendsto S).comp hS
      exact tendsto_nhds_unique (hT0 (D.J N y)) t1
    rw [e]; exact S.continuous
  let T : StrongDual ℂ (SchwartzBruhat G) := ⟨TL, hTc⟩
  refine ⟨T, ?_⟩
  show Tendsto id 𝒢 (𝓝 T)
  rw [(dws (E := SchwartzBruhat G)).tendsto_nhds]
  intro B ε hε
  have hV : {p : StrongDual ℂ (SchwartzBruhat G) × StrongDual ℂ (SchwartzBruhat G) |
      dsn B (p.2 - p.1) < ε / 2} ∈ uniformity (StrongDual ℂ (SchwartzBruhat G)) := by
    rw [uniformity_eq_comap_nhds_zero]
    show (fun p : StrongDual ℂ (SchwartzBruhat G) × StrongDual ℂ (SchwartzBruhat G) => p.2 - p.1) ⁻¹'
      (dsn B ⁻¹' Iio (ε / 2)) ∈ _
    refine preimage_mem_comap ((dsn_cont B).continuousAt.preimage_mem_nhds ?_)
    rw [map_zero]; exact Iio_mem_nhds (half_pos hε)
  obtain ⟨A, hA, hAV⟩ := mem_prod_same_iff.1 (h𝒢.2 hV)
  filter_upwards [hA] with S hS
  refine lt_of_le_of_lt (dsn_le B _ (half_pos hε).le fun x hx => ?_) (half_lt_self hε)
  have t : Tendsto (fun S' : StrongDual ℂ (SchwartzBruhat G) => ‖S' x - S x‖) 𝒢
      (𝓝 ‖T x - S x‖) :=
    ((continuous_norm.comp (continuous_id.sub continuous_const)).tendsto (T0 x)).comp (hT0 x)
  have h2 : ‖T x - S x‖ ≤ ε / 2 := by
    refine le_of_tendsto t ?_
    filter_upwards [hA] with S' hS'
    have := hAV (mk_mem_prod hS hS')
    simp only [Set.mem_ofPred_eq] at this
    have h3 := le_dsn B (S' - S) hx
    rw [sub_apply] at h3
    exact h3.trans this.le
  rw [sub_apply, norm_sub_rev]
  exact h2

end dual

/-! ### the stages -/

section stagesX

variable (D : SBData G)

def XS (N : ℕ) : Submodule ℂ (SchwartzBruhat G) := LinearMap.range (D.J N)

lemma XS_mono : Monotone (XS D) := by
  intro N M h x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨D.P M (D.J N y), pl_of_le D (pl_J D N y) h⟩

lemma XS_exh (x : SchwartzBruhat G) : ∃ N, x ∈ XS D N := by
  obtain ⟨N, hN⟩ := level D x
  exact ⟨N, D.P N x, hN⟩

def Rn (N : ℕ) : XS D N →L[ℂ] ESp (D.m N) (D.s N) (D.d N) :=
  ⟨(D.P N).comp (XS D N).subtype, (P_cont D N).comp continuous_subtype_val⟩

def Prn (N : ℕ) : ESp (D.m N) (D.s N) (D.d N) →L[ℂ] XS D N :=
  ⟨LinearMap.codRestrict (XS D N) (D.J N) fun y => ⟨y, rfl⟩,
    continuous_induced_rng.2 (J_cont D N)⟩

lemma Prn_Rn (N : ℕ) (x : XS D N) : Prn D N (Rn D N x) = x := by
  obtain ⟨_, y, rfl⟩ := x
  apply Subtype.ext
  show D.J N (D.P N (D.J N y)) = D.J N y
  rw [D.PJ]

lemma Rn_emb (N : ℕ) : IsEmbedding (Rn D N) :=
  Function.LeftInverse.isEmbedding (f := Prn D N) (Prn_Rn D N) (Prn D N).continuous
    (Rn D N).continuous

lemma XS_ws (N : ℕ) : WithSeminorms (fun q : {q : Seminorm ℂ (XS D N) // Continuous q} => q.1) := by
  have h : WithSeminorms (SeminormFamily.comp (sn (m := D.m N) (n := 0) (r := 0) (d := D.d N))
      (Rn D N).toLinearMap) :=
    (Rn_emb D N).isInducing.withSeminorms es_ws
  exact ws_all h

lemma XS_t2 (N : ℕ) : T2Space (XS D N) := by
  haveI := sb_t2 D
  infer_instance

lemma XS_ctvs (N : ℕ) : IsCompleteTVS (XS D N) := by
  haveI := XS_t2 D N
  refine ⟨inferInstance, fun 𝒻 h𝒻 => ?_⟩
  obtain ⟨hne, hc⟩ := h𝒻
  obtain ⟨z, hz⟩ := es_lim (D.hd N) (map (Rn D N) 𝒻) fun U hU => by
    obtain ⟨A, hA, hAU⟩ := hc _ ((Rn D N).continuous.tendsto 0 (by rw [map_zero]; exact hU))
    refine ⟨Rn D N '' A, image_mem_map hA, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_sub]; exact hAU x hx y hy
  refine ⟨Prn D N z, ?_⟩
  have e : 𝒻 = map (Prn D N) (map (Rn D N) 𝒻) := by
    rw [Filter.map_map]
    have : (Prn D N ∘ Rn D N : XS D N → XS D N) = id := funext (Prn_Rn D N)
    rw [this, Filter.map_id]
  rw [e]
  exact (Filter.map_mono hz).trans ((Prn D N).continuous.tendsto z)

lemma XS_frechet (N : ℕ) : IsFrechet (XS D N) := by
  haveI := es_metrizable (m := D.m N) (n := 0) (r := 0) (D.hd N)
  exact ⟨lc_of_ws (XS_ws D N), XS_ctvs D N, (Rn_emb D N).metrizableSpace⟩

lemma XS_nuclear (N : ℕ) : IsNuclear (XS D N) := by
  haveI := XS_t2 D N
  have h0 : ∀ f : ESp (D.m N) (D.s N) (D.d N),
      HasSum (fun j : JJ (D.m N) 0 0 (D.s N) => φE (D.hd N) j f • eE j) f := hexpE (D.hd N)
  have h1 := tr_exp (E := XS D N) (X := ESp (D.m N) (D.s N) (D.d N)) (ι := JJ (D.m N) 0 0 (D.s N))
    (φE (D.hd N)) eE h0 (Rn D N) (Prn D N) (Prn_Rn D N)
  have h2 := tr_dom (E := XS D N) (X := ESp (D.m N) (D.s N) (D.d N)) (ι := JJ (D.m N) 0 0 (D.s N))
    (φE (D.hd N)) eE cw (hdomE (D.hd N)) (Rn D N) (Prn D N)
  refine nuclear_of_frame (XS_ws D N) (fun j => (φE (D.hd N) j).comp (Rn D N))
    (fun j => Prn D N (eE j)) cw ?_ ?_ ?_ ?_
  · exact h1
  · exact cw_pos
  · exact cw_summable
  · exact h2

lemma stage_fac (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : ∃ M, ∃ φ : ElemSchwartz m n r s d → XS D M, Continuous φ ∧
      SchwartzBruhat.ofElem Γ k π hs hπ = Subtype.val ∘ φ := by
  obtain ⟨M, h1, h2⟩ := D.stage Γ k m n r s d π hs hπ
  refine ⟨M, fun g => ⟨D.J M (D.P M (SchwartzBruhat.ofElem Γ k π hs hπ g)), ⟨_, rfl⟩⟩,
    continuous_induced_rng.2 ((J_cont D M).comp h2), ?_⟩
  funext g; exact (h1 g).symm

lemma top_eq_LF : (inferInstance : TopologicalSpace (SchwartzBruhat G)) =
    sInf {t | IsLocallyConvexTopology (SchwartzBruhat G) t ∧
      ∀ n, @Continuous (XS D n) (SchwartzBruhat G) _ t Subtype.val} := by
  have key := stage_fac D
  refine le_antisymm ?_ (sInf_le ⟨sb_lc, fun n => continuous_subtype_val⟩)
  refine le_sInf fun t ht => ?_
  refine sInf_le ⟨ht.1, fun Γ k m n r s d π hs hπ => ?_⟩
  obtain ⟨M, φ, hφ, e⟩ := key Γ k m n r s d π hs hπ
  rw [e]
  exact @Continuous.comp _ _ _ _ (@instTopologicalSpaceSubtype _ _ (instTopologicalSpaceSchwartzBruhat G))
    t _ _ (ht.2 M) hφ

end stagesX

/-! ### the main abstract theorem -/

theorem sb_all (D : SBData G) :
    IsStrictLFOfNuclearFrechet (SchwartzBruhat G) ∧ IsStrictLF (SchwartzBruhat G) ∧
    IsHLCS (SchwartzBruhat G) ∧ IsCompleteTVS (SchwartzBruhat G) ∧
    IsNuclear (SchwartzBruhat G) ∧ IsMontel (SchwartzBruhat G) ∧
    IsCompleteTVS (StrongDual ℂ (SchwartzBruhat G)) ∧
    IsNuclear (StrongDual ℂ (SchwartzBruhat G)) ∧ IsMontel (StrongDual ℂ (SchwartzBruhat G)) := by
  haveI := sb_t2 D
  haveI := sb_complete D
  haveI := dual_complete D
  have hws := sb_ws (G := G)
  have hsr : ∀ Ψ : StrongDual ℂ (StrongDual ℂ (SchwartzBruhat G)),
      ∃! x : SchwartzBruhat G, ∀ T : StrongDual ℂ (SchwartzBruhat G), Ψ T = T x := by
    intro Ψ
    refine srefl hws (Phi D) (Evec D) (Cw D) ?_ ?_ ?_ ?_ Ψ
    · exact frame_exp D
    · exact Cw_pos D
    · exact Cw_summable D
    · exact frame_dom D
  have hlf : IsStrictLFOfNuclearFrechet (SchwartzBruhat G) :=
    ⟨XS D, XS_mono D, XS_exh D, fun n => ⟨XS_frechet D n, XS_nuclear D n⟩, top_eq_LF D⟩
  refine ⟨hlf, ⟨XS D, XS_mono D, XS_exh D, fun n => XS_frechet D n, top_eq_LF D⟩,
    ⟨sb_lc, inferInstance⟩, sb_ctvs D, ?_, ⟨⟨sb_lc, inferInstance⟩, ?_, hsr, sbE hws⟩,
    ctvs_of_complete, ?_, ⟨⟨lc_of_ws (dws (E := SchwartzBruhat G)), inferInstance⟩, ?_,
      drefl hws hsr⟩⟩
  · refine nuclear_of_frame hws (Phi D) (Evec D) (Cw D) ?_ ?_ ?_ ?_
    · exact frame_exp D
    · exact Cw_pos D
    · exact Cw_summable D
    · exact frame_dom D
  · intro B hBc hBb
    refine frame_compact hws (Phi D) (Evec D) (Cw D) ?_ ?_ ?_ ?_ B hBc hBb
    · exact frame_exp D
    · exact Cw_pos D
    · exact Cw_summable D
    · exact frame_dom D
  · refine dual_nuclear_of_frame hws (Phi D) (Evec D) (Cw D) ?_ ?_ ?_ ?_
    · exact frame_exp D
    · exact Cw_pos D
    · exact Cw_summable D
    · exact frame_dom D
  · intro A hAc hAb
    refine dual_compact hws (Phi D) (Evec D) (Cw D) ?_ ?_ ?_ ?_ A hAc hAb
    · exact frame_exp D
    · exact Cw_pos D
    · exact Cw_summable D
    · exact frame_dom D

end

end Aux_LF





namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set

noncomputable section

section pb

variable {m m' n' r' s' s : ℕ} {d' : Fin s' → ℕ} {d : Fin s → ℕ} [∀ i, NeZero (d i)]

open Classical in
/-- pull back along `(x, b) ↦ (A x, 0, 0, 0) + c b` (zero where `P b` fails) -/
def pbFun (A : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) (P : ((i : Fin s) → ZMod (d i)) → Prop)
    (c : ((i : Fin s) → ZMod (d i)) → ElemGroup m' n' r' s' d')
    (g : ElemGroup m' n' r' s' d' → ℂ) : ElemGroup m 0 0 s d → ℂ :=
  fun q => if P q.2.2.2 then g ((A q.1, 0, 0, 0) + c q.2.2.2) else 0

/-- a lift of the torus part -/
def tlift (z : Fin n' → UnitAddCircle) : Fin n' → ℝ :=
  fun l => Classical.choose (QuotientAddGroup.mk_surjective (z l))

lemma tlift_spec (z : Fin n' → UnitAddCircle) :
    (fun l => ((tlift z l : ℝ) : UnitAddCircle)) = z :=
  funext fun l => Classical.choose_spec (QuotientAddGroup.mk_surjective (z l))

/-- the linear part of the pull back on `XT` -/
def pbL (A : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) :
    ((Fin m → ℝ) × (Fin 0 → ℝ)) →L[ℝ] ((Fin m' → ℝ) × (Fin n' → ℝ)) :=
  (A.comp (ContinuousLinearMap.fst ℝ _ _)).prod 0

lemma pbL_apply (A : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) (xt : (Fin m → ℝ) × (Fin 0 → ℝ)) :
    pbL (n' := n') A xt = (A xt.1, 0) := rfl

open Classical in
lemma lift_pb (A : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) (P : ((i : Fin s) → ZMod (d i)) → Prop)
    (c : ((i : Fin s) → ZMod (d i)) → ElemGroup m' n' r' s' d')
    (g : ElemGroup m' n' r' s' d' → ℂ) (a : Fin 0 → ℤ) (b : (i : Fin s) → ZMod (d i)) :
    elemLift (pbFun A P c g) a b = if P b then
      (fun xt => elemLift g (c b).2.2.1 (c b).2.2.2 (pbL A xt + ((c b).1, tlift (c b).2.1)))
      else 0 := by
  funext xt
  by_cases hP : P b
  · simp only [elemLift, pbFun, hP, if_true, pbL_apply]
    congr 1
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · rfl
    · show (0 : Fin n' → UnitAddCircle) + (c b).2.1 = fun j => (((0 + tlift (c b).2.1) j : ℝ) : UnitAddCircle)
      rw [zero_add, zero_add]; exact (tlift_spec _).symm
    · show (0 : Fin r' → ℤ) + (c b).2.2.1 = _; rw [zero_add]
    · show (0 : (i : Fin s') → ZMod (d' i)) + (c b).2.2.2 = _; rw [zero_add]
  · simp only [elemLift, pbFun, hP, if_false]; rfl

lemma iter_pb {F : ((Fin m' → ℝ) × (Fin n' → ℝ)) → ℂ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (A : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ))
    (v : (Fin m' → ℝ) × (Fin n' → ℝ)) (k : ℕ) (xt : (Fin m → ℝ) × (Fin 0 → ℝ)) :
    ‖iteratedFDeriv ℝ k (fun xt => F (pbL A xt + v)) xt‖ ≤
      ‖iteratedFDeriv ℝ k F (pbL A xt + v)‖ * ‖pbL (n' := n') A‖ ^ k := by
  have hF' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => F (z + v)) :=
    hF.comp (contDiff_id.add contDiff_const)
  have h1 : (fun xt => F (pbL A xt + v)) = (fun z => F (z + v)) ∘ pbL A := rfl
  rw [h1, (pbL A).iteratedFDeriv_comp_right hF' xt (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma pow_bound (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (i : ℕ) :
    (p + q) ^ i ≤ 2 ^ i * (p ^ i + q ^ i) := by
  have h1 : p + q ≤ 2 * max p q := by
    have := le_max_left p q; have := le_max_right p q; linarith
  have h2 : (max p q) ^ i ≤ p ^ i + q ^ i := by
    rcases le_total p q with h | h
    · rw [max_eq_right h]; have := pow_nonneg hp i; linarith
    · rw [max_eq_left h]; have := pow_nonneg hq i; linarith
  calc (p + q) ^ i ≤ (2 * max p q) ^ i := pow_le_pow_left₀ (by positivity) h1 i
    _ = 2 ^ i * (max p q) ^ i := mul_pow _ _ _
    _ ≤ 2 ^ i * (p ^ i + q ^ i) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- the pointwise estimate -/
lemma pb_est (A : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖x‖ ≤ K * ‖A x‖) (P : ((i : Fin s) → ZMod (d i)) → Prop)
    (c : ((i : Fin s) → ZMod (d i)) → ElemGroup m' n' r' s' d')
    (g : ES m' n' r' s' d') (i k : ℕ) (a : Fin 0 → ℤ) (b : (i : Fin s) → ZMod (d i))
    (xt : (Fin m → ℝ) × (Fin 0 → ℝ)) :
    ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift (pbFun A P c g.toFun) a b) xt‖ ≤
      (K ^ i * 2 ^ i * ‖pbL (n' := n') A‖ ^ k * (∑ b', ‖(c b').1‖ ^ i + 1)) *
        (sn (i, 0, k) g + sn (0, 0, k) g) := by
  classical
  rw [lift_pb]
  have hS1 : 0 ≤ sn (i, 0, k) g := apply_nonneg _ _
  have hS0 : 0 ≤ sn (0, 0, k) g := apply_nonneg _ _
  have hsum0 : 0 ≤ ∑ b', ‖(c b').1‖ ^ i := Finset.sum_nonneg fun _ _ => by positivity
  by_cases hP : P b
  · simp only [hP, if_true]
    set v : (Fin m' → ℝ) × (Fin n' → ℝ) := ((c b).1, tlift (c b).2.1)
    set y := pbL (n' := n') A xt + v
    have hD := iter_pb (lift_smooth g (c b).2.2.1 (c b).2.2.2) A v k xt
    have hy1 : y.1 = A xt.1 + (c b).1 := rfl
    have hq1 := le_sn (i, 0, k) g ((c b).2.2.1, (c b).2.2.2, y)
    have hq0 := le_sn (0, 0, k) g ((c b).2.2.1, (c b).2.2.2, y)
    simp only [pow_zero, one_mul] at hq1 hq0
    have hx : ‖xt.1‖ ≤ K * (‖y.1‖ + ‖(c b).1‖) := by
      refine (hK xt.1).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      have : A xt.1 = y.1 - (c b).1 := by rw [hy1]; abel
      rw [this]; exact norm_sub_le _ _
    have hxi : ‖xt.1‖ ^ i ≤ K ^ i * (2 ^ i * (‖y.1‖ ^ i + ‖(c b).1‖ ^ i)) := by
      calc ‖xt.1‖ ^ i ≤ (K * (‖y.1‖ + ‖(c b).1‖)) ^ i := pow_le_pow_left₀ (norm_nonneg _) hx i
        _ = K ^ i * (‖y.1‖ + ‖(c b).1‖) ^ i := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_bound _ _ (norm_nonneg _) (norm_nonneg _) i)
            (by positivity)
    have hcb : ‖(c b).1‖ ^ i ≤ ∑ b', ‖(c b').1‖ ^ i :=
      Finset.single_le_sum (f := fun b' => ‖(c b').1‖ ^ i) (fun _ _ => by positivity)
        (Finset.mem_univ b)
    set D := ‖iteratedFDeriv ℝ k (elemLift g.toFun (c b).2.2.1 (c b).2.2.2) y‖
    set Lk := ‖pbL (n' := n') A‖ ^ k
    have hD0 : 0 ≤ D := norm_nonneg _
    have hLk : 0 ≤ Lk := by positivity
    calc ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k
          (fun xt => elemLift g.toFun (c b).2.2.1 (c b).2.2.2 (pbL A xt + v)) xt‖
        ≤ (K ^ i * (2 ^ i * (‖y.1‖ ^ i + ‖(c b).1‖ ^ i))) * (D * Lk) :=
          mul_le_mul hxi hD (norm_nonneg _) (by positivity)
      _ = K ^ i * 2 ^ i * Lk * (‖y.1‖ ^ i * D + ‖(c b).1‖ ^ i * D) := by ring
      _ ≤ K ^ i * 2 ^ i * Lk * (sn (i, 0, k) g + (∑ b', ‖(c b').1‖ ^ i) * sn (0, 0, k) g) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hq1 ?_) (by positivity)
          exact mul_le_mul hcb hq0 hD0 hsum0
      _ ≤ _ := by
          rw [mul_assoc (K ^ i * 2 ^ i * Lk)]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h7 := mul_nonneg hsum0 hS1
          have h8 : (∑ b', ‖(c b').1‖ ^ i + 1) * (sn (i, 0, k) g + sn (0, 0, k) g) =
            (∑ b', ‖(c b').1‖ ^ i) * sn (i, 0, k) g + (∑ b', ‖(c b').1‖ ^ i) * sn (0, 0, k) g +
              sn (i, 0, k) g + sn (0, 0, k) g := by ring
          rw [h8]; linarith
  · simp only [hP, if_false]
    have : iteratedFDeriv ℝ k (0 : (Fin m → ℝ) × (Fin 0 → ℝ) → ℂ) xt = 0 := by
      rw [show (0 : (Fin m → ℝ) × (Fin 0 → ℝ) → ℂ) = fun _ => 0 from rfl, iteratedFDeriv_zero_fun]
      rfl
    rw [this, norm_zero, mul_zero]
    positivity

lemma pb_rd (A : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖x‖ ≤ K * ‖A x‖) (P : ((i : Fin s) → ZMod (d i)) → Prop)
    (c : ((i : Fin s) → ZMod (d i)) → ElemGroup m' n' r' s' d') (g : ES m' n' r' s' d') :
    IsRapidDecay (pbFun A P c g.toFun) := by
  classical
  refine ⟨fun a b => ?_, fun i j k => ?_⟩
  · rw [lift_pb]
    split_ifs
    · exact (lift_smooth g _ _).comp ((pbL A).contDiff.add contDiff_const)
    · exact contDiff_const
  · refine ⟨(K ^ i * 2 ^ i * ‖pbL (n' := n') A‖ ^ k * (∑ b', ‖(c b').1‖ ^ i + 1)) *
        (sn (i, 0, k) g + sn (0, 0, k) g), fun a b xt => ?_⟩
    have ha : ‖a‖ = 0 := by rw [Subsingleton.elim a 0, norm_zero]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · rw [hj, pow_zero, one_mul]; exact pb_est A K hK0 hK P c g i k a b xt
    · rw [ha, zero_pow hj.ne', zero_mul, zero_mul]
      have := pb_est A K hK0 hK P c g i k a b xt
      exact (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)).trans this

/-- the pull back as a linear map of elementary Schwartz spaces -/
def pbLin (A : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖x‖ ≤ K * ‖A x‖) (P : ((i : Fin s) → ZMod (d i)) → Prop)
    (c : ((i : Fin s) → ZMod (d i)) → ElemGroup m' n' r' s' d') :
    ES m' n' r' s' d' →ₗ[ℂ] ES m 0 0 s d where
  toFun g := ⟨pbFun A P c g.toFun, Submodule.subset_span (pb_rd A K hK0 hK P c g)⟩
  map_add' f g := by
    apply Subtype.ext
    funext q
    show pbFun A P c (f + g).toFun q = pbFun A P c f.toFun q + pbFun A P c g.toFun q
    classical
    simp only [pbFun]
    split_ifs
    · rfl
    · simp
  map_smul' z g := by
    apply Subtype.ext
    funext q
    show pbFun A P c (z • g).toFun q = z • pbFun A P c g.toFun q
    classical
    simp only [pbFun]
    split_ifs
    · rfl
    · simp

lemma pbLin_apply (A : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖x‖ ≤ K * ‖A x‖) (P : ((i : Fin s) → ZMod (d i)) → Prop)
    (c : ((i : Fin s) → ZMod (d i)) → ElemGroup m' n' r' s' d') (g : ES m' n' r' s' d') :
    (pbLin (d := d) A K hK0 hK P c g).toFun = pbFun A P c g.toFun := rfl

lemma pbLin_cont (A : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖x‖ ≤ K * ‖A x‖) (P : ((i : Fin s) → ZMod (d i)) → Prop)
    (c : ((i : Fin s) → ZMod (d i)) → ElemGroup m' n' r' s' d') :
    Continuous (pbLin (d := d) A K hK0 hK P c) := by
  refine WithSeminorms.continuous_of_isBounded es_ws es_ws _ fun p => ?_
  obtain ⟨i, j, k⟩ := p
  set κ := K ^ i * 2 ^ i * ‖pbL (n' := n') A‖ ^ k * (∑ b', ‖(c b').1‖ ^ i + 1)
  have hκ : 0 ≤ κ := by positivity
  refine ⟨{(i, 0, k), (0, 0, k)}, ⟨2 * κ, by positivity⟩, fun g => ?_⟩
  show sn (i, j, k) (pbLin A K hK0 hK P c g) ≤ (2 * κ) * ((({(i, 0, k), (0, 0, k)} :
    Finset (ℕ × ℕ × ℕ)).sup sn) g)
  have h1 : sn (i, 0, k) g ≤ (({(i, 0, k), (0, 0, k)} : Finset (ℕ × ℕ × ℕ)).sup sn) g :=
    Seminorm.le_finset_sup_apply (Finset.mem_insert_self _ _)
  have h2 : sn (0, 0, k) g ≤ (({(i, 0, k), (0, 0, k)} : Finset (ℕ × ℕ × ℕ)).sup sn) g :=
    Seminorm.le_finset_sup_apply (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine sn_le _ _ (by positivity) fun a b xt => ?_
  have ha : ‖a‖ = 0 := by rw [Subsingleton.elim a 0, norm_zero]
  have hest := pb_est A K hK0 hK P c g i k a b xt
  rw [pbLin_apply] at *
  have hb : κ * (sn (i, 0, k) g + sn (0, 0, k) g) ≤ 2 * κ *
      ((({(i, 0, k), (0, 0, k)} : Finset (ℕ × ℕ × ℕ)).sup sn) g) := by nlinarith
  rcases Nat.eq_zero_or_pos j with hj | hj
  · show ‖a‖ ^ j * ‖xt.1‖ ^ i * _ ≤ _
    rw [hj, pow_zero, one_mul]; exact hest.trans hb
  · show ‖a‖ ^ j * ‖xt.1‖ ^ i * _ ≤ _
    rw [ha, zero_pow hj.ne', zero_mul, zero_mul]
    exact (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)).trans (hest.trans hb)

end pb

end

end Aux_LFA

namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set
open scoped Pointwise

noncomputable section

/-! ### compactness of sets of characters (adapted from Mathlib's local compactness proof) -/

section dualcpt

variable {X Y : Type*} [TopologicalSpace X] [Group X] [IsTopologicalGroup X]
  [UniformSpace Y] [CommGroup Y] [IsUniformGroup Y] [T0Space Y] [CompactSpace Y]

lemma cpt_of_equi (U : Set X) (V W : Set Y) (hU : IsCompact U) (hWV : W ⊆ V) (hWc : IsClosed W)
    (h : EquicontinuousAt (fun f : {f : X →* Y | Set.MapsTo f U V} ↦ (f : X → Y)) 1) :
    IsCompact {f : ContinuousMonoidHom X Y | Set.MapsTo f U W} := by
  replace h := equicontinuous_of_equicontinuousAt_one _ h
  let S1 : Set (X →* Y) := {f | Set.MapsTo f U W}
  let S2 : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U W}
  let S3 : Set C(X, Y) := (↑) '' S2
  let S4 : Set (X → Y) := (↑) '' S3
  replace h : Equicontinuous ((↑) : S1 → X → Y) :=
    h.comp (Subtype.map _root_.id fun f hf ↦ hf.mono_right hWV)
  have hS4 : S4 = (↑) '' S1 := by
    ext
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 → X → Y) := by
    rw [equicontinuous_iff_range, ← Set.image_eq_range] at h ⊢
    rwa [← hS4] at h
  replace hS4 : S4 = Set.pi U (fun _ ↦ W) ∩ Set.range ((↑) : (X →* Y) → (X → Y)) := by
    simp_rw [hS4, Set.ext_iff, Set.mem_image, S1, Set.mem_ofPred_eq]
    exact fun f ↦ ⟨fun ⟨g, hg, hf⟩ ↦ hf ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hf⟩ ↦ ⟨g, hf ▸ hg, hf⟩⟩
  replace hS4 : IsClosed S4 :=
    hS4.symm ▸ (isClosed_set_pi (fun _ _ ↦ hWc)).inter (MonoidHom.isClosed_range_coe X Y)
  exact (ContinuousMonoidHom.isInducing_toContinuousMap X Y).isCompact_iff.mpr
      (ArzelaAscoli.isCompact_of_equicontinuous S3 hS4.isCompact h)

lemma equi_of_basis (U0 : Set X) (hU0o : U0 ∈ 𝓝 (1 : X)) (V : ℕ → Set Y)
    (hV : ∀ {n x}, x ∈ V n → x * x ∈ V n → x ∈ V (n + 1))
    (hVo : Filter.HasBasis (nhds 1) (fun _ ↦ True) V) :
    EquicontinuousAt (fun f : {f : X →* Y | Set.MapsTo f U0 (V 0)} ↦ (f : X → Y)) 1 := by
  let U_aux : ℕ → {S : Set X | S ∈ nhds 1} :=
    Nat.rec ⟨U0, hU0o⟩ <| fun _ S ↦ let h := exists_closed_nhds_one_inv_eq_mul_subset S.2
      ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let U : ℕ → Set X := fun n ↦ (U_aux n).1
  have hU1 : ∀ n, U n ∈ nhds 1 := fun n ↦ (U_aux n).2
  have hU2 : ∀ n, U (n + 1) * U (n + 1) ⊆ U n :=
    fun n ↦ (Classical.choose_spec (exists_closed_nhds_one_inv_eq_mul_subset (U_aux n).2)).2.2.2
  have hU3 : ∀ n, U (n + 1) ⊆ U n :=
    fun n x hx ↦ hU2 n (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds (hU1 (n + 1))))
  have hU4 : ∀ f : X →* Y, Set.MapsTo f (U 0) (V 0) → ∀ n, Set.MapsTo f (U n) (V n) := by
    intro f hf n
    induction n with
    | zero => exact hf
    | succ n ih =>
      exact fun x hx ↦ hV (ih (hU3 n hx)) (map_mul f x x ▸ ih (hU2 n (Set.mul_mem_mul hx hx)))
  rw [hVo.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  refine fun n _ ↦ Filter.eventually_iff_exists_mem.mpr ⟨U n, hU1 n, fun x hx ⟨f, hf⟩ ↦ ?_⟩
  rw [Set.mem_ofPred_eq, map_one, div_one]
  exact hU4 f hf n hx

end dualcpt

/-- closed half-plane-type neighbourhood of `1` in the circle -/
def Wc : Set Circle := {z | (1 / 2 : ℝ) ≤ (z : ℂ).re}

lemma Wc_closed : IsClosed Wc :=
  isClosed_le continuous_const (Complex.continuous_re.comp continuous_subtype_val)

lemma Wo_open : IsOpen {z : Circle | (1 / 2 : ℝ) < (z : ℂ).re} :=
  isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)

lemma Wo_sub : {z : Circle | (1 / 2 : ℝ) < (z : ℂ).re} ⊆ interior Wc :=
  interior_maximal (fun z (hz : (1 / 2 : ℝ) < (z : ℂ).re) => (le_of_lt hz : (1 / 2 : ℝ) ≤ (z : ℂ).re)) Wo_open

lemma one_mem_Wo : (1 : Circle) ∈ {z : Circle | (1 / 2 : ℝ) < (z : ℂ).re} := by
  show (1 / 2 : ℝ) < ((1 : Circle) : ℂ).re
  rw [Circle.coe_one, Complex.one_re]; norm_num

lemma Wc_sub : Wc ⊆ Circle.centeredArc (Real.pi / 2) := by
  intro z hz
  rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
  have h : 0 < (z : ℂ).re := lt_of_lt_of_le (by norm_num) hz
  exact Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h)

lemma cpt_char {X : Type*} [TopologicalSpace X] [Group X] [IsTopologicalGroup X]
    (U : Set X) (hUc : IsCompact U) (hU1 : U ∈ 𝓝 (1 : X)) :
    IsCompact {f : ContinuousMonoidHom X Circle | Set.MapsTo f U Wc} := by
  let Vn : ℕ → Set Circle := fun n ↦ Circle.centeredArc (Real.pi / 2 ^ (n + 1))
  have hVn : ∀ n x, x ∈ Vn n ↔ |Complex.arg x| < Real.pi / 2 ^ (n + 1) :=
    fun n x ↦ Circle.mem_centeredArc (z := x)
      (div_le_self Real.pi_nonneg (one_le_pow₀ one_le_two))
  have hV : ∀ {n x}, x ∈ Vn n → x * x ∈ Vn n → x ∈ Vn (n + 1) := by
    intro n x h1 h2
    rw [hVn] at h1 h2 ⊢
    rwa [Circle.coe_mul, Complex.arg_mul x.coe_ne_zero x.coe_ne_zero,
      ← two_mul, abs_mul, abs_two, ← lt_div_iff₀' two_pos, div_div, ← pow_succ] at h2
    apply Set.Ioo_subset_Ioc_self
    rw [← two_mul, Set.mem_Ioo, ← abs_lt, abs_mul, abs_two, ← lt_div_iff₀' two_pos]
    refine h1.trans_le ?_
    gcongr
    exact le_self_pow₀ one_le_two n.succ_ne_zero
  have hVo : Filter.HasBasis (nhds (1 : Circle)) (fun _ ↦ True) Vn := by
    simpa [Vn] using Circle.hasBasis_centeredArc_div_two_pow
  have h0 : Vn 0 = Circle.centeredArc (Real.pi / 2) := by simp [Vn]
  have he := equi_of_basis U hU1 Vn hV hVo
  rw [h0] at he
  exact cpt_of_equi U _ Wc hUc Wc_sub Wc_closed he

/-! ### the annihilator as a subgroup -/

section annsub

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- the annihilator as a subgroup of the dual -/
def annSub (k : Subgroup G) : Subgroup (PontryaginDual G) where
  carrier := annihilator k
  mul_mem' {χ ψ} hχ hψ x hx := by
    show χ x * ψ x = 1
    rw [hχ x hx, hψ x hx, one_mul]
  one_mem' x _ := rfl
  inv_mem' {χ} hχ x hx := by
    show (χ x)⁻¹ = 1
    rw [hχ x hx, inv_one]

lemma annihilator_closed (k : Subgroup G) : IsClosed (annihilator k) := by
  have : annihilator k = ⋂ x ∈ k, {χ : PontryaginDual G | χ x = 1} := by
    ext χ; simp [annihilator]
  rw [this]
  refine isClosed_biInter fun x _ => isClosed_eq ?_ continuous_const
  exact (continuous_eval_const x : Continuous fun χ : ContinuousMonoidHom G Circle => χ x)

lemma annihilator_open_of_compact (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    IsOpen (annihilator k) := by
  let V : Set (PontryaginDual G) :=
    {ψ | Set.MapsTo ψ (k : Set G) (Circle.centeredArc (Real.pi / 2))}
  have hVopen : IsOpen V :=
    isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hk (Circle.isOpen_centeredArc _))
  have hVeq : V = annihilator k := by
    ext ψ
    refine ⟨fun hψ a ha ↦ ?_, fun hψ a ha ↦ ?_⟩
    · refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ ↦ ?_
      rw [← map_pow]
      exact hψ (k.pow_mem ha n)
    · rw [hψ a ha, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
      simp [Real.pi_pos]
  rw [← hVeq]; exact hVopen

end annsub

/-! ### the generic setting -/

/-- a group `A ≅ ℝ^m × B`, with a filtration of `B` by compact open subgroups -/
structure Setup (A : Type*) [AddCommGroup A] [TopologicalSpace A] (B : Type*) [AddCommGroup B]
    [TopologicalSpace B] (m : ℕ) where
  e : ((Fin m → ℝ) × B) ≃+ A
  he : Continuous e
  hes : Continuous e.symm
  L : ℕ → AddSubgroup B
  M : ℕ → AddSubgroup B
  L_open : ∀ N, IsOpen (L N : Set B)
  L_cpt : ∀ N, IsCompact (L N : Set B)
  M_open : ∀ N, IsOpen (M N : Set B)
  M_cpt : ∀ N, IsCompact (M N : Set B)
  L_mono : Monotone L
  M_anti : Antitone M
  ML : ∀ N, M N ≤ L N
  L_cov : ∀ y, ∃ N, y ∈ L N
  M_small : ∀ W ∈ 𝓝 (0 : B), ∃ N, (M N : Set B) ⊆ W

namespace Setup

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {m : ℕ}
  (S : Setup A B m)

/-- vector coordinate -/
def X (z : Multiplicative A) : Fin m → ℝ := (S.e.symm (Multiplicative.toAdd z)).1
/-- `B` coordinate -/
def Y (z : Multiplicative A) : B := (S.e.symm (Multiplicative.toAdd z)).2
/-- the point with coordinates `(x, y)` -/
def emb (x : Fin m → ℝ) (y : B) : Multiplicative A := Multiplicative.ofAdd (S.e (x, y))

@[simp] lemma X_emb (x y) : S.X (S.emb x y) = x := by simp [X, emb]
@[simp] lemma Y_emb (x y) : S.Y (S.emb x y) = y := by simp [Y, emb]
lemma emb_XY (z : Multiplicative A) : S.emb (S.X z) (S.Y z) = z := by
  simp [X, Y, emb]
lemma emb_mul (x y x' y') : S.emb x y * S.emb x' y' = S.emb (x + x') (y + y') := by
  simp only [emb, ← ofAdd_add, ← map_add, Prod.mk_add_mk]
@[simp] lemma X_mul (z w) : S.X (z * w) = S.X z + S.X w := by
  simp [X, toAdd_mul, map_add]
@[simp] lemma Y_mul (z w) : S.Y (z * w) = S.Y z + S.Y w := by
  simp [Y, toAdd_mul, map_add]
@[simp] lemma X_one : S.X 1 = 0 := by simp [X]
@[simp] lemma Y_one : S.Y 1 = 0 := by simp [Y]
@[simp] lemma X_inv (z) : S.X z⁻¹ = -S.X z := by simp [X, toAdd_inv, map_neg]
@[simp] lemma Y_inv (z) : S.Y z⁻¹ = -S.Y z := by simp [Y, toAdd_inv, map_neg]
@[simp] lemma X_pow (z) (n : ℕ) : S.X (z ^ n) = n • S.X z := by simp [X, toAdd_pow, map_nsmul]
@[simp] lemma Y_pow (z) (n : ℕ) : S.Y (z ^ n) = n • S.Y z := by simp [Y, toAdd_pow, map_nsmul]
lemma emb_zero : S.emb 0 0 = 1 := by simp [emb]
lemma emb_split (x y) : S.emb x y = S.emb x 0 * S.emb 0 y := by rw [emb_mul]; simp
lemma emb_pow (x y) (n : ℕ) : S.emb x y ^ n = S.emb (n • x) (n • y) := by
  conv_lhs => rw [← S.emb_XY (S.emb x y ^ n)]
  simp
lemma ext_XY {z w : Multiplicative A} (h1 : S.X z = S.X w) (h2 : S.Y z = S.Y w) : z = w := by
  rw [← S.emb_XY z, ← S.emb_XY w, h1, h2]

lemma cont_X : Continuous S.X :=
  continuous_fst.comp (S.hes.comp continuous_toAdd)
lemma cont_Y : Continuous S.Y :=
  continuous_snd.comp (S.hes.comp continuous_toAdd)
lemma cont_emb : Continuous (fun p : (Fin m → ℝ) × B => S.emb p.1 p.2) :=
  continuous_ofAdd.comp S.he

/-- the stage groups `Γ_N = ℝ^m × L_N` -/
def Gam (N : ℕ) : Subgroup (Multiplicative A) where
  carrier := {z | S.Y z ∈ S.L N}
  mul_mem' {z w} hz hw := by
    show S.Y (z * w) ∈ S.L N
    rw [Y_mul]; exact add_mem hz hw
  one_mem' := by show S.Y 1 ∈ S.L N; rw [Y_one]; exact zero_mem _
  inv_mem' {z} hz := by show S.Y z⁻¹ ∈ S.L N; rw [Y_inv]; exact neg_mem hz

/-- the stage groups `k_N = 0 × M_N` -/
def Kk (N : ℕ) : Subgroup (Multiplicative A) where
  carrier := {z | S.X z = 0 ∧ S.Y z ∈ S.M N}
  mul_mem' {z w} hz hw := by
    refine ⟨?_, ?_⟩
    · rw [X_mul, hz.1, hw.1, add_zero]
    · rw [Y_mul]; exact add_mem hz.2 hw.2
  one_mem' := ⟨S.X_one, by rw [Y_one]; exact zero_mem _⟩
  inv_mem' {z} hz := ⟨by rw [X_inv, hz.1, neg_zero], by rw [Y_inv]; exact neg_mem hz.2⟩

lemma mem_Gam {N z} : z ∈ S.Gam N ↔ S.Y z ∈ S.L N := Iff.rfl
lemma mem_Kk {N z} : z ∈ S.Kk N ↔ S.X z = 0 ∧ S.Y z ∈ S.M N := Iff.rfl

lemma Kk_le (N : ℕ) : S.Kk N ≤ S.Gam N := fun _ hz => S.ML N hz.2

lemma Gam_open (N : ℕ) : IsOpen (S.Gam N : Set (Multiplicative A)) :=
  (S.L_open N).preimage S.cont_Y

lemma M_closed (N : ℕ) : IsClosed (S.M N : Set B) :=
  AddSubgroup.isClosed_of_isOpen _ (S.M_open N)

lemma Kk_closed (N : ℕ) : IsClosed (S.Kk N : Set (Multiplicative A)) :=
  (isClosed_eq S.cont_X continuous_const).inter ((S.M_closed N).preimage S.cont_Y)

lemma Kk_eq_image (N : ℕ) : (S.Kk N : Set (Multiplicative A)) =
    (fun p : (Fin m → ℝ) × B => S.emb p.1 p.2) '' ({0} ×ˢ (S.M N : Set B)) := by
  ext z
  constructor
  · intro hz
    exact ⟨(S.X z, S.Y z), ⟨hz.1, hz.2⟩, S.emb_XY z⟩
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact ⟨by simpa using h1, by simpa using h2⟩

lemma Kk_cpt (N : ℕ) : IsCompact (S.Kk N : Set (Multiplicative A)) := by
  rw [Kk_eq_image]
  exact (isCompact_singleton.prod (S.M_cpt N)).image S.cont_emb

/-- `x ↦ x / n` -/
lemma emb_div (x : Fin m → ℝ) (n : ℕ) (hn : n ≠ 0) :
    S.emb x 0 = S.emb ((n : ℝ)⁻¹ • x) 0 ^ n := by
  rw [emb_pow, smul_zero, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

lemma Gam_cg (N : ℕ) : IsCompactlyGeneratedSubgroup (S.Gam N) := by
  let f := fun p : (Fin m → ℝ) × B => S.emb p.1 p.2
  refine ⟨f '' (Metric.closedBall 0 1 ×ˢ (S.L N : Set B)),
    ((isCompact_closedBall _ _).prod (S.L_cpt N)).image S.cont_emb, ?_,
    ⟨{z | ‖S.X z‖ < 1}, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨p, ⟨_, h2⟩, rfl⟩
    show S.Y (S.emb p.1 p.2) ∈ S.L N
    simpa using h2
  · refine (isOpen_lt (continuous_norm.comp S.cont_X) continuous_const).mem_nhds ?_
    show ‖S.X 1‖ < 1
    simp
  · rintro z ⟨h1, h2⟩
    exact ⟨(S.X z, S.Y z), ⟨mem_closedBall_zero_iff.2 (le_of_lt h1), h2⟩, S.emb_XY z⟩
  · refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
    · rintro _ ⟨p, ⟨_, h2⟩, rfl⟩
      show S.Y (S.emb p.1 p.2) ∈ S.L N
      simpa using h2
    · intro z hz
      obtain ⟨n, hn⟩ := exists_nat_gt ‖S.X z‖
      have hn0 : n ≠ 0 := by
        rintro rfl; simp at hn; exact absurd hn (not_lt.2 (norm_nonneg _))
      rw [← S.emb_XY z, S.emb_split, S.emb_div _ n hn0]
      refine mul_mem (pow_mem (Subgroup.subset_closure (show S.emb ((n : ℝ)⁻¹ • S.X z) 0 ∈
        f '' (Metric.closedBall 0 1 ×ˢ (S.L N : Set B)) from ⟨((n : ℝ)⁻¹ • S.X z, 0), ⟨?_, zero_mem _⟩,
        rfl⟩)) _) (Subgroup.subset_closure (show S.emb 0 (S.Y z) ∈
        f '' (Metric.closedBall 0 1 ×ˢ (S.L N : Set B)) from ⟨(0, S.Y z), ⟨by simp, hz⟩, rfl⟩))
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_natCast]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      rw [inv_mul_le_iff₀ hnpos, mul_one]; exact le_of_lt hn

/-- the endomorphism `z ↦ (0, Y z)` -/
def Ef : ContinuousMonoidHom (Multiplicative A) (Multiplicative A) where
  toFun z := S.emb 0 (S.Y z)
  map_one' := by simp [emb_zero]
  map_mul' z w := by simp [emb_mul]
  continuous_toFun := S.cont_emb.comp (continuous_const.prodMk S.cont_Y)

/-- the endomorphism `z ↦ (X z / n, 0)` -/
def En (n : ℕ) : ContinuousMonoidHom (Multiplicative A) (Multiplicative A) where
  toFun z := S.emb ((n : ℝ)⁻¹ • S.X z) 0
  map_one' := by simp [emb_zero]
  map_mul' z w := by simp [emb_mul, smul_add]
  continuous_toFun := by
    exact S.cont_emb.comp (((S.cont_X.const_smul ((n : ℝ)⁻¹)).prodMk continuous_const :
      Continuous fun z => (((n : ℝ)⁻¹ • S.X z), (0 : B))))

lemma ann_cg (N : ℕ) : ∃ H : Subgroup (PontryaginDual (Multiplicative A)),
    (H : Set (PontryaginDual (Multiplicative A))) = annihilator (S.Kk N) ∧
      IsCompactlyGeneratedSubgroup H := by
  let K : Set (Multiplicative A) := {z | ‖S.X z‖ ≤ 1 ∧ S.Y z ∈ S.M N}
  have hKeq : K = (fun p : (Fin m → ℝ) × B => S.emb p.1 p.2) ''
      (Metric.closedBall 0 1 ×ˢ (S.M N : Set B)) := by
    ext z
    constructor
    · intro hz; exact ⟨(S.X z, S.Y z), ⟨mem_closedBall_zero_iff.2 hz.1, hz.2⟩, S.emb_XY z⟩
    · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using mem_closedBall_zero_iff.1 h1, by simpa using h2⟩
  have hKc : IsCompact K := by
    rw [hKeq]; exact ((isCompact_closedBall _ _).prod (S.M_cpt N)).image S.cont_emb
  have hK1 : K ∈ 𝓝 (1 : Multiplicative A) := by
    have hO : IsOpen {z : Multiplicative A | ‖S.X z‖ < 1 ∧ S.Y z ∈ S.M N} :=
      (isOpen_lt (continuous_norm.comp S.cont_X) continuous_const).inter
        ((S.M_open N).preimage S.cont_Y)
    refine Filter.mem_of_superset (hO.mem_nhds ⟨by simp, by simp [zero_mem]⟩) ?_
    rintro z ⟨h1, h2⟩; exact ⟨le_of_lt h1, h2⟩
  let H := annSub (S.Kk N)
  let C : Set (PontryaginDual (Multiplicative A)) :=
    {χ | Set.MapsTo χ K Wc} ∩ annihilator (S.Kk N)
  refine ⟨H, rfl, C,
    (cpt_char K hKc hK1).inter_right (annihilator_closed _), fun _ h => h.2,
    ⟨{χ | Set.MapsTo χ K (interior Wc)}, ?_, ?_⟩, ?_⟩
  · refine IsOpen.mem_nhds (isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hKc
      isOpen_interior)) ?_
    intro z _
    exact Wo_sub one_mem_Wo
  · rintro χ ⟨h1, h2⟩
    exact ⟨fun z hz => interior_subset (h1 hz), h2⟩
  · refine le_antisymm ((Subgroup.closure_le _).2 fun χ h => h.2) ?_
    intro χ hχ
    -- continuity of `x ↦ χ (x, 0)` at `0`
    have hc : Continuous fun x : Fin m → ℝ => χ (S.emb x 0) :=
      χ.continuous.comp (S.cont_emb.comp (continuous_id.prodMk continuous_const))
    have hev : ∀ᶠ x in 𝓝 (0 : Fin m → ℝ), χ (S.emb x 0) ∈ {z : Circle | (1 / 2 : ℝ) < (z : ℂ).re} := by
      refine hc.continuousAt.preimage_mem_nhds (Wo_open.mem_nhds ?_)
      rw [emb_zero, map_one]; exact one_mem_Wo
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    let χf : PontryaginDual (Multiplicative A) := χ.comp S.Ef
    let ψ : PontryaginDual (Multiplicative A) := χ.comp (S.En (n + 1))
    have hEf : ∀ z, S.Ef z = S.emb 0 (S.Y z) := fun _ => rfl
    have hEn : ∀ z, S.En (n + 1) z = S.emb (((n + 1 : ℕ) : ℝ)⁻¹ • S.X z) 0 := fun _ => rfl
    have hfac : χ = χf * ψ ^ (n + 1) := by
      refine PontryaginDual.ext fun z => ?_
      have h1 : (χf * ψ ^ (n + 1)) z = χf z * (ψ z) ^ (n + 1) :=
        (ContinuousMonoidHom.mul_apply (E := Circle) χf (ψ ^ (n + 1)) z).trans
          (congrArg (χf z * ·) (ContinuousMonoidHom.pow_apply (E := Circle) ψ (n + 1) z))
      rw [h1]
      show χ z = χ (S.Ef z) * χ (S.En (n + 1) z) ^ (n + 1)
      rw [hEf, hEn, ← map_pow, ← S.emb_div _ _ (Nat.succ_ne_zero n), ← map_mul, mul_comm,
        ← S.emb_split, S.emb_XY]
    have hχf : χf ∈ C := by
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · have : S.Ef z ∈ S.Kk N := ⟨by simp [hEf], by simpa [hEf] using hz.2⟩
        show χ (S.Ef z) ∈ Wc
        rw [hχ _ this]
        show (1 / 2 : ℝ) ≤ ((1 : Circle) : ℂ).re
        rw [Circle.coe_one, Complex.one_re]; norm_num
      · have : S.Ef z ∈ S.Kk N := ⟨by simp [hEf], by simpa [hEf] using hz.2⟩
        exact hχ _ this
    have hψ : ψ ∈ C := by
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · show χ (S.En (n + 1) z) ∈ Wc
        rw [hEn]
        have hd : dist ((((n + 1 : ℕ) : ℝ))⁻¹ • S.X z) 0 < δ := by
          rw [dist_zero_right, norm_smul, norm_inv, Real.norm_natCast]
          calc (((n + 1 : ℕ) : ℝ))⁻¹ * ‖S.X z‖ ≤ (((n + 1 : ℕ) : ℝ))⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left hz.1 (by positivity)
            _ = 1 / ((n : ℝ) + 1) := by push_cast; ring
            _ < δ := hn
        have hb := hball hd
        simp only [Set.mem_setOf_eq] at hb
        exact hb.le
      · show χ (S.En (n + 1) z) = 1
        rw [hEn, hz.1, smul_zero, emb_zero, map_one]
    rw [hfac]
    exact mul_mem (Subgroup.subset_closure hχf) (pow_mem (Subgroup.subset_closure hψ) _)

lemma Kk_good (N : ℕ) : IsGoodSubgroup (S.Kk N) :=
  ⟨S.Kk_closed N, annihilator_open_of_compact _ (S.Kk_cpt N), S.ann_cg N⟩

lemma stage_sp (N : ℕ) : IsStructuralPair (S.Gam N) (S.Kk N) :=
  ⟨S.Gam_open N, S.Gam_cg N, S.Kk_good N, S.Kk_le N⟩

end Setup

end

end Aux_LFA

namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set

noncomputable section

lemma fin_struct (Q : Type*) [AddCommGroup Q] [Finite Q] :
    ∃ (s : ℕ) (d : Fin s → ℕ), (∀ i, d i ≠ 0) ∧ Nonempty (Q ≃+ ((i : Fin s) → ZMod (d i))) := by
  obtain ⟨ι, fι, p, hp, ex, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite Q
  let σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => p (σ.symm j) ^ ex (σ.symm j), fun j =>
    pow_ne_zero _ (hp _).ne_zero, ⟨?_⟩⟩
  exact (f.trans (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (p i ^ ex i))).toAddEquiv).trans
    (RingEquiv.piCongrLeft' (fun i => ZMod (p i ^ ex i)) σ).toAddEquiv

namespace Setup

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {m : ℕ}
  (S : Setup A B m)

/-- the finite quotient `L_N / M_N` -/
abbrev Q (N : ℕ) : Type _ := ↥(S.L N) ⧸ (S.M N).addSubgroupOf (S.L N)

instance finQ (N : ℕ) : Finite (S.Q N) := by
  haveI : CompactSpace ↥(S.L N) := isCompact_iff_compactSpace.mp (S.L_cpt N)
  exact AddSubgroup.quotient_finite_of_isOpen _ ((S.M_open N).preimage continuous_subtype_val)

lemma ex_struct (N : ℕ) : ∃ (s : ℕ) (d : Fin s → ℕ), (∀ i, d i ≠ 0) ∧
    Nonempty (S.Q N ≃+ ((i : Fin s) → ZMod (d i))) := fin_struct _

/-- number of cyclic factors -/
def sN (N : ℕ) : ℕ := (S.ex_struct N).choose
/-- orders -/
def dN (N : ℕ) : Fin (S.sN N) → ℕ := (S.ex_struct N).choose_spec.choose
lemma hdN (N : ℕ) (i) : S.dN N i ≠ 0 := (S.ex_struct N).choose_spec.choose_spec.1 i
instance neZ (N : ℕ) (i) : NeZero (S.dN N i) := ⟨S.hdN N i⟩
/-- the structure isomorphism -/
def eps (N : ℕ) : S.Q N ≃+ ((i : Fin (S.sN N)) → ZMod (S.dN N i)) :=
  Classical.choice (S.ex_struct N).choose_spec.choose_spec.2

/-- the finite coordinate -/
def del (N : ℕ) (y : ↥(S.L N)) : (i : Fin (S.sN N)) → ZMod (S.dN N i) :=
  S.eps N (QuotientAddGroup.mk y)

lemma del_add (N : ℕ) (y y' : ↥(S.L N)) : S.del N (y + y') = S.del N y + S.del N y' := by
  simp [del, QuotientAddGroup.mk_add]

lemma del_eq_iff (N : ℕ) (y y' : ↥(S.L N)) :
    S.del N y = S.del N y' ↔ ((y' : B) - y) ∈ S.M N := by
  unfold del
  rw [(S.eps N).injective.eq_iff, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  simp [sub_eq_neg_add]

lemma del_zero_iff (N : ℕ) (y : ↥(S.L N)) : S.del N y = 0 ↔ (y : B) ∈ S.M N := by
  have h := S.del_eq_iff N 0 y
  have h0 : S.del N 0 = 0 := by simp [del]
  rw [h0] at h
  rw [eq_comm, h]; simp

lemma del_surj (N : ℕ) : Function.Surjective (S.del N) := by
  intro b
  obtain ⟨q, hq⟩ := (S.eps N).surjective b
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact ⟨y, hq⟩

/-! ### nested sets of representatives -/

/-- `R` is a set of representatives of `L_N / M_N` -/
def IsRep (N : ℕ) (R : Set B) : Prop :=
  R ⊆ S.L N ∧ ∀ y ∈ S.L N, ∃! r, r ∈ R ∧ y - r ∈ S.M N

lemma ext_rep (N : ℕ) (T : Set B) (hT : T ⊆ S.L N)
    (hTp : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ S.M N → a = b) :
    ∃ R, T ⊆ R ∧ S.IsRep N R := by
  classical
  let q : B → B ⧸ S.M N := QuotientAddGroup.mk
  have hq : ∀ a b, q a = q b ↔ a - b ∈ S.M N := by
    intro a b
    rw [QuotientAddGroup.eq]
    constructor
    · intro h; have := neg_mem h; simpa [sub_eq_add_neg, add_comm] using this
    · intro h; have := neg_mem h; simpa [sub_eq_add_neg, add_comm] using this
  let R : Set B := T ∪ {r | r ∈ S.L N ∧ (∀ t ∈ T, q t ≠ q r) ∧ (q r).out = r}
  refine ⟨R, subset_union_left, ?_, ?_⟩
  · rintro r (hr | ⟨hr, -, -⟩)
    · exact hT hr
    · exact hr
  · intro y hy
    by_cases hex : ∃ t ∈ T, q t = q y
    · obtain ⟨t, ht, hty⟩ := hex
      refine ⟨t, ⟨Or.inl ht, (hq y t).1 hty.symm⟩, ?_⟩
      rintro r ⟨hr | ⟨_, hr2, _⟩, hyr⟩
      · exact hTp r hr t ht (by
          have h1 := (hq y r).2 hyr
          exact (hq r t).1 (h1.symm.trans hty.symm))
      · exact absurd (hty.trans ((hq y r).2 hyr)) (hr2 t ht)
    · simp only [not_exists, not_and] at hex
      have hout : q (q y).out = q y := by simp [q]
      refine ⟨(q y).out, ⟨Or.inr ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · have h1 : y - (q y).out ∈ S.M N := (hq y _).1 hout.symm
        have h2 : (q y).out = y - (y - (q y).out) := by abel
        rw [h2]; exact sub_mem hy (S.ML N h1)
      · intro t ht; rw [hout]; exact hex t ht
      · rw [hout]
      · exact (hq y _).1 hout.symm
      · rintro r ⟨hr | ⟨_, _, hr3⟩, hyr⟩
        · exact absurd ((hq y r).2 hyr).symm (hex r hr)
        · rw [← hr3, (hq y r).2 hyr]

lemma isRep_succ {N : ℕ} {R : Set B} (hR : S.IsRep N R) :
    ∃ R', R ⊆ R' ∧ S.IsRep (N + 1) R' := by
  refine S.ext_rep (N + 1) R (hR.1.trans (S.L_mono (Nat.le_succ N))) fun a ha b hb hab => ?_
  have hab' : a - b ∈ S.M N := S.M_anti (Nat.le_succ N) hab
  obtain ⟨r, _, hr⟩ := hR.2 a (hR.1 ha)
  have h1 := hr a ⟨ha, by simp [zero_mem]⟩
  have h2 := hr b ⟨hb, hab'⟩
  rw [h1, h2]

lemma isRep_zero : ∃ R, S.IsRep 0 R := by
  obtain ⟨R, -, h⟩ := S.ext_rep 0 ∅ (empty_subset _) (by simp)
  exact ⟨R, h⟩

/-- the sequence of nested representative sets -/
def RR : (N : ℕ) → {R : Set B // S.IsRep N R}
  | 0 => ⟨S.isRep_zero.choose, S.isRep_zero.choose_spec⟩
  | N + 1 => ⟨(S.isRep_succ (RR N).2).choose, (S.isRep_succ (RR N).2).choose_spec.2⟩

lemma RR_succ (N : ℕ) : (S.RR N).1 ⊆ (S.RR (N + 1)).1 := by
  show _ ⊆ (S.isRep_succ (S.RR N).2).choose
  exact (S.isRep_succ (S.RR N).2).choose_spec.1

lemma RR_mono {N M : ℕ} (h : N ≤ M) : (S.RR N).1 ⊆ (S.RR M).1 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (S.RR_succ _)

/-- the representative of `b ∈ L_N/M_N` -/
def rep (N : ℕ) (b : (i : Fin (S.sN N)) → ZMod (S.dN N i)) : B :=
  ((S.RR N).2.2 _ ((S.del_surj N b).choose).2).exists.choose

lemma rep_spec (N : ℕ) (b) : S.rep N b ∈ (S.RR N).1 ∧
    (((S.del_surj N b).choose : B) - S.rep N b) ∈ S.M N :=
  ((S.RR N).2.2 _ ((S.del_surj N b).choose).2).exists.choose_spec

lemma rep_mem (N : ℕ) (b) : S.rep N b ∈ S.L N := (S.RR N).2.1 (S.rep_spec N b).1

lemma del_rep (N : ℕ) (b) : S.del N ⟨S.rep N b, S.rep_mem N b⟩ = b := by
  have h := (S.del_eq_iff N ⟨S.rep N b, S.rep_mem N b⟩ (S.del_surj N b).choose).2
    (S.rep_spec N b).2
  rw [h]; exact (S.del_surj N b).choose_spec

lemma rep_del_of_mem (N : ℕ) (y : B) (hy : y ∈ (S.RR N).1) :
    S.rep N (S.del N ⟨y, (S.RR N).2.1 hy⟩) = y := by
  set b := S.del N ⟨y, (S.RR N).2.1 hy⟩
  have h1 : ((S.del_surj N b).choose : B) - y ∈ S.M N :=
    (S.del_eq_iff N ⟨y, (S.RR N).2.1 hy⟩ (S.del_surj N b).choose).1
      ((S.del_surj N b).choose_spec).symm
  obtain ⟨r, _, hr⟩ := (S.RR N).2.2 _ ((S.del_surj N b).choose).2
  rw [hr _ (S.rep_spec N b), hr _ ⟨hy, h1⟩]

lemma rep_nested {N M : ℕ} (h : N ≤ M) (b) :
    S.rep M (S.del M ⟨S.rep N b, S.L_mono h (S.rep_mem N b)⟩) = S.rep N b :=
  S.rep_del_of_mem M _ (S.RR_mono h (S.rep_spec N b).1)

/-! ### the presentations of the stages -/

/-- the presentation `Γ_N → ℝ^m × ∏ ℤ/d_i` -/
def pres (N : ℕ) : S.Gam N →* Multiplicative (ElemGroup m 0 0 (S.sN N) (S.dN N)) where
  toFun z := Multiplicative.ofAdd (S.X z, 0, 0, S.del N ⟨S.Y z, z.2⟩)
  map_one' := by
    have h : S.del N ⟨S.Y ((1 : S.Gam N) : Multiplicative A), (1 : S.Gam N).2⟩ = 0 := by
      rw [del_zero_iff]; show S.Y 1 ∈ S.M N; rw [Y_one]; exact zero_mem _
    simp only [OneMemClass.coe_one, X_one] at h ⊢
    rw [h]; rfl
  map_mul' z w := by
    have h : S.del N ⟨S.Y ((z * w : S.Gam N) : Multiplicative A), (z * w).2⟩ =
        S.del N ⟨S.Y z, z.2⟩ + S.del N ⟨S.Y w, w.2⟩ := by
      rw [← del_add]; congr 1; apply Subtype.ext; simp
    rw [h]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul, Subgroup.coe_mul, X_mul, Prod.mk_add_mk, add_zero]

lemma pres_apply (N : ℕ) (z : S.Gam N) :
    Multiplicative.toAdd (S.pres N z) = (S.X z, 0, 0, S.del N ⟨S.Y z, z.2⟩) := rfl

/-- the section of the presentation -/
def sec (N : ℕ) (q : ElemGroup m 0 0 (S.sN N) (S.dN N)) : Multiplicative A :=
  S.emb q.1 (S.rep N q.2.2.2)

lemma sec_mem (N : ℕ) (q) : S.sec N q ∈ S.Gam N := by
  show S.Y (S.emb _ _) ∈ S.L N; rw [Y_emb]; exact S.rep_mem N _

lemma pres_sec (N : ℕ) (q) : Multiplicative.toAdd (S.pres N ⟨S.sec N q, S.sec_mem N q⟩) = q := by
  rw [pres_apply]
  refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_))
  · simp [sec]
  · show S.del N _ = q.2.2.2
    have : (⟨S.Y (S.sec N q), S.sec_mem N q⟩ : ↥(S.L N)) =
        ⟨S.rep N q.2.2.2, S.rep_mem N q.2.2.2⟩ := Subtype.ext (by simp [sec])
    rw [this, del_rep]

lemma cont_del (N : ℕ) : Continuous fun z : S.Gam N => S.del N ⟨S.Y z, z.2⟩ := by
  rw [continuous_discrete_rng]
  intro b
  obtain ⟨y0, hy0⟩ := S.del_surj N b
  have : (fun z : S.Gam N => S.del N ⟨S.Y z, z.2⟩) ⁻¹' {b} =
      Subtype.val ⁻¹' (S.Y ⁻¹' ((fun y => y - (y0 : B)) ⁻¹' (S.M N : Set B))) := by
    ext z
    simp only [mem_preimage, mem_singleton_iff]
    rw [← hy0, del_eq_iff]
    show (y0 : B) - S.Y z ∈ S.M N ↔ S.Y z - (y0 : B) ∈ S.M N
    rw [← neg_sub, neg_mem_iff]
  rw [this]
  exact (((S.M_open N).preimage (continuous_id.sub continuous_const)).preimage S.cont_Y).preimage
    continuous_subtype_val

lemma pres_isElem (N : ℕ) : IsElemPresentation (S.Gam N) (S.Kk N) (S.pres N) := by
  refine ⟨S.hdN N, ?_, ?_, ?_, ?_⟩
  · refine continuous_ofAdd.comp ?_
    exact (S.cont_X.comp continuous_subtype_val).prodMk
      (continuous_const.prodMk (continuous_const.prodMk (S.cont_del N)))
  · intro U hU
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨z, hzU, rfl⟩
    obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU
    have hzO : (z : Multiplicative A) ∈ O := by rw [← hOU] at hzU; exact hzU
    have hpre : IsOpen ((fun x => S.emb x (S.Y z)) ⁻¹' O) :=
      hO.preimage (S.cont_emb.comp (continuous_id.prodMk continuous_const))
    have hzx : S.X z ∈ (fun x => S.emb x (S.Y z)) ⁻¹' O := by
      show S.emb (S.X z) (S.Y z) ∈ O; rw [emb_XY]; exact hzO
    refine ⟨{w | (Multiplicative.toAdd w).1 ∈ (fun x => S.emb x (S.Y z)) ⁻¹' O ∧
      (Multiplicative.toAdd w).2.2.2 = S.del N ⟨S.Y z, z.2⟩}, ?_, ?_, ?_⟩
    · rintro w ⟨hw1, hw2⟩
      have hmem : S.emb (Multiplicative.toAdd w).1 (S.Y z) ∈ S.Gam N := by
        show S.Y _ ∈ S.L N; rw [Y_emb]; exact z.2
      refine ⟨⟨_, hmem⟩, ?_, ?_⟩
      · rw [← hOU]; exact hw1
      · apply Multiplicative.toAdd.injective
        rw [pres_apply]
        refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_))
        · simp
        · show S.del N _ = (Multiplicative.toAdd w).2.2.2
          rw [hw2]; congr 1; apply Subtype.ext; simp
    · refine IsOpen.inter (hpre.preimage (continuous_fst.comp continuous_toAdd)) ?_
      have hc : Continuous fun w : Multiplicative (ElemGroup m 0 0 (S.sN N) (S.dN N)) =>
          (Multiplicative.toAdd w).2.2.2 :=
        continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd))
      exact (isOpen_discrete ({S.del N ⟨S.Y z, z.2⟩} : Set ((i : Fin (S.sN N)) → ZMod (S.dN N i)))).preimage hc
    · exact ⟨hzx, rfl⟩
  · intro w
    refine ⟨⟨S.sec N (Multiplicative.toAdd w), S.sec_mem N _⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [pres_sec]
  · intro z
    constructor
    · intro h
      have h1 := congrArg Multiplicative.toAdd h
      rw [pres_apply, toAdd_one] at h1
      have hx : S.X z = 0 := congrArg Prod.fst h1
      have hd : S.del N ⟨S.Y z, z.2⟩ = 0 := congrArg (fun p => p.2.2.2) h1
      exact ⟨hx, (S.del_zero_iff N _).1 hd⟩
    · rintro ⟨hx, hy⟩
      apply Multiplicative.toAdd.injective
      rw [pres_apply, toAdd_one, hx, (S.del_zero_iff N ⟨S.Y z, z.2⟩).2 hy]
      rfl

end Setup

end

end Aux_LFA

namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set

noncomputable section

/-! ### no small subgroups in elementary groups -/

lemma vec_small {m : ℕ} (x : Fin m → ℝ) (h : ∀ j : ℕ, ‖j • x‖ < 1) : x = 0 := by
  by_contra hx
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / ‖x‖)
  have := h j
  rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast] at this
  rw [div_lt_iff₀ hpos] at hj
  linarith

lemma circ_norm {u : ℝ} (hu : |u| ≤ 1 / 2) : ‖((u : ℝ) : UnitAddCircle)‖ = |u| :=
  (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by rw [abs_one]; exact hu)

lemma circ_small (t : UnitAddCircle) (h : ∀ j : ℕ, ‖j • t‖ < 1 / 4) : t = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
  set u := x - (round x : ℝ) with hu_def
  have h0 : (((round x : ℤ) : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨round x, by simp⟩
  have hxu : (QuotientAddGroup.mk x : UnitAddCircle) = ((u : ℝ) : UnitAddCircle) := by
    show ((x : ℝ) : UnitAddCircle) = _
    rw [hu_def, AddCircle.coe_sub, h0, sub_zero]
  rw [hxu] at h ⊢
  have hu2 : |u| ≤ 1 / 2 := abs_sub_round x
  have hu4 : |u| < 1 / 4 := by
    have := h 1; rw [one_smul, circ_norm hu2] at this; exact this
  by_cases hu0 : u = 0
  · rw [hu0]; rfl
  have hpos : 0 < |u| := abs_pos.2 hu0
  set j := ⌈1 / (4 * |u|)⌉₊
  have hj1 : 1 / (4 * |u|) ≤ j := Nat.le_ceil _
  have hj2 : (j : ℝ) < 1 / (4 * |u|) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk1 : 1 / 4 ≤ (j : ℝ) * |u| := by
    have := mul_le_mul_of_nonneg_right hj1 hpos.le
    rwa [show 1 / (4 * |u|) * |u| = 1 / 4 by field_simp] at this
  have hk2 : (j : ℝ) * |u| < 1 / 2 := by
    have := mul_lt_mul_of_pos_right hj2 hpos
    rw [add_mul, show 1 / (4 * |u|) * |u| = 1 / 4 by field_simp, one_mul] at this
    linarith
  have hju : |(j • u : ℝ)| = (j : ℝ) * |u| := by
    rw [nsmul_eq_mul, abs_mul, Nat.abs_cast]
  have := h j
  rw [← AddCircle.coe_nsmul, circ_norm (by rw [hju]; exact hk2.le), hju] at this
  linarith

lemma nss (m n r s : ℕ) (d : Fin s → ℕ) [∀ i, NeZero (d i)] :
    ∃ W ∈ 𝓝 (0 : ElemGroup m n r s d), ∀ w, (∀ j : ℕ, j • w ∈ W) → w = 0 := by
  refine ⟨{w | ‖w.1‖ < 1 ∧ ‖w.2.1‖ < 1 / 4 ∧ w.2.2 = 0}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ ⟨by simp, by simp, rfl⟩
    refine (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      ((isOpen_lt (continuous_norm.comp (continuous_fst.comp continuous_snd)) continuous_const).inter
        ?_)
    have hc : Continuous fun w : ElemGroup m n r s d => w.2.2 := continuous_snd.comp continuous_snd
    exact (isOpen_discrete ({0} : Set ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))))).preimage hc
  · intro w hw
    have h1 : w.1 = 0 := vec_small _ fun j => by simpa using (hw j).1
    have h2 : w.2.1 = 0 := by
      funext i
      refine circ_small _ fun j => lt_of_le_of_lt ?_ (hw j).2.1
      have := norm_le_pi_norm (j • w.2.1) i
      simpa using this
    have h3 : w.2.2 = 0 := by simpa using (hw 1).2.2
    exact Prod.ext h1 (Prod.ext h2 h3)

lemma disc_zero {m : ℕ} {D : Type*} [AddCommGroup D] [TopologicalSpace D] [DiscreteTopology D]
    (ψ : (Fin m → ℝ) →+ D) (hψ : Continuous ψ) (x : Fin m → ℝ) : ψ x = 0 := by
  have ho : IsOpen (ψ ⁻¹' {0}) := (isOpen_discrete _).preimage hψ
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 ho 0 (by simp)
  obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ / δ)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hmem : (n : ℝ)⁻¹ • x ∈ Metric.ball (0 : Fin m → ℝ) δ := by
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hn0]
    rwa [div_lt_iff₀ hδ] at hn
  have h1 : ψ ((n : ℝ)⁻¹ • x) = 0 := hball hmem
  have h2 : x = n • ((n : ℝ)⁻¹ • x) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
  rw [h2, map_nsmul, h1, smul_zero]

/-! ### the generic `ell_zero` -/

section ellz

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

lemma ell_zero {k : Subgroup (Multiplicative A)} (hk : IsOpen (annihilator k))
    (ℓ : A →+ ℝ) (hℓ : Continuous ℓ) (x : Multiplicative A)
    (hx : x ∈ k) : ℓ (Multiplicative.toAdd x) = 0 := by
  let χ : ℝ → PontryaginDual (Multiplicative A) := fun t =>
    ({ toFun := fun y => Circle.exp (t * ℓ (Multiplicative.toAdd y))
       map_one' := by
         simp only [toAdd_one, map_zero, mul_zero, Circle.exp_zero]
       map_mul' := by
         intro a b
         simp only [toAdd_mul, map_add, mul_add, Circle.exp_add]
       continuous_toFun := Circle.exp.continuous.comp
         (continuous_const.mul (hℓ.comp continuous_toAdd)) } :
      ContinuousMonoidHom (Multiplicative A) Circle)
  have hχ : Continuous χ := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact Circle.exp.continuous.comp
      (continuous_fst.mul (hℓ.comp (continuous_toAdd.comp continuous_snd)))
  have h0 : χ 0 ∈ annihilator k := by
    intro y _
    show Circle.exp (0 * ℓ (Multiplicative.toAdd y)) = 1
    rw [zero_mul, Circle.exp_zero]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), χ t ∈ annihilator k :=
    hχ.continuousAt.preimage_mem_nhds (hk.mem_nhds h0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  by_contra hne
  generalize hc : ℓ (Multiplicative.toAdd x) = c at hne
  have hcpos : 0 < |c| := abs_pos.mpr hne
  let t : ℝ := min (δ / 2) (1 / (|c| + 1))
  have htpos : 0 < t := lt_min (by linarith) (by positivity)
  have htd : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h1 : (χ t) x = 1 := hball htd x hx
  have h2 : Circle.exp (t * c) = 1 := by
    rw [← hc]
    exact h1
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 h2
  have h3 : |t * c| < 1 := by
    rw [abs_mul, abs_of_pos htpos]
    have h4 : t ≤ 1 / (|c| + 1) := min_le_right _ _
    have h5 : t * |c| ≤ 1 / (|c| + 1) * |c| := mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
    have h6 : 1 / (|c| + 1) * |c| < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith
    linarith
  have hn0 : n = 0 := by
    by_contra hn0
    have h7 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      exact_mod_cast this
    have h8 : |t * c| = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hn, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h9 : (1 : ℝ) * (2 * Real.pi) ≤ |(n : ℝ)| * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right h7 (by positivity)
    have h10 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  rw [hn0, Int.cast_zero, zero_mul] at hn
  have : c = 0 := by
    rcases mul_eq_zero.1 hn with h | h
    · exact absurd h htpos.ne'
    · exact h
  exact hne this

end ellz

/-! ### classification of the structural pairs -/

namespace Setup

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {m : ℕ}
  (S : Setup A B m)

lemma vec_ker {k : Subgroup (Multiplicative A)} (hk : IsOpen (annihilator k)) (x : Fin m → ℝ)
    (hx : S.emb x 0 ∈ k) : x = 0 := by
  funext i
  let ℓ : A →+ ℝ :=
    { toFun := fun a => (S.e.symm a).1 i
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hℓ : Continuous ℓ := (continuous_apply i).comp (continuous_fst.comp S.hes)
  have := ell_zero hk ℓ hℓ _ hx
  simpa [ℓ, emb] using this

variable {Γ k : Subgroup (Multiplicative A)}

lemma gam_bound (hs : IsStructuralPair Γ k) : ∃ M, ∀ z ∈ Γ, S.Y z ∈ S.L M := by
  obtain ⟨U, hUc, -, -, hcl⟩ := hs.2.1
  obtain ⟨M, hM⟩ := (hUc.image S.cont_Y).elim_directed_cover (fun N => (S.L N : Set B))
    (fun N => S.L_open N) (fun y _ => mem_iUnion.2 (S.L_cov y)) S.L_mono.directed_le
  refine ⟨M, fun z hz => ?_⟩
  have hle : Γ ≤ S.Gam M := by
    rw [← hcl]
    exact (Subgroup.closure_le _).2 fun u hu => hM ⟨u, hu, rfl⟩
  exact hle hz

lemma gam_vec (hs : IsStructuralPair Γ k) :
    (∀ x, S.emb x 0 ∈ Γ) ∧ ∃ K0, ∀ y ∈ S.M K0, S.emb 0 y ∈ Γ := by
  have hP : IsOpen ((fun p : (Fin m → ℝ) × B => S.emb p.1 p.2) ⁻¹' (Γ : Set (Multiplicative A))) :=
    hs.1.preimage S.cont_emb
  have h0 : ((0 : Fin m → ℝ), (0 : B)) ∈
      (fun p : (Fin m → ℝ) × B => S.emb p.1 p.2) ⁻¹' (Γ : Set (Multiplicative A)) := by
    show S.emb 0 0 ∈ Γ; rw [emb_zero]; exact one_mem _
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hP.mem_nhds h0)
  obtain ⟨K0, hK0⟩ := S.M_small v hv
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hu
  refine ⟨fun x => ?_, K0, fun y hy => by exact huv (Set.mk_mem_prod (mem_of_mem_nhds hu) (hK0 hy))⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ / δ)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  rw [S.emb_div x n (by exact_mod_cast hn0.ne')]
  have hb : (n : ℝ)⁻¹ • x ∈ Metric.ball (0 : Fin m → ℝ) δ := by
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hn0]
    rwa [div_lt_iff₀ hδ] at hn
  exact pow_mem (by exact huv (Set.mk_mem_prod (hball hb) (mem_of_mem_nhds hv))) _

lemma emb_mem_iff (hs : IsStructuralPair Γ k) (x : Fin m → ℝ) (y : B) :
    S.emb x y ∈ Γ ↔ S.emb 0 y ∈ Γ := by
  have hv := (S.gam_vec hs).1
  rw [S.emb_split x y]
  constructor
  · intro h
    have := mul_mem (inv_mem (hv x)) h
    rwa [inv_mul_cancel_left] at this
  · intro h; exact mul_mem (hv x) h

lemma kk_sub {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    {π : Γ →* Multiplicative (ElemGroup m' n' r' s' d')}
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    ∃ M, ∀ y ∈ S.M M, S.emb 0 y ∈ k := by
  haveI : ∀ i, NeZero (d' i) := fun i => ⟨hπ.1 i⟩
  obtain ⟨W, hW, hWs⟩ := nss m' n' r' s' d'
  obtain ⟨K0, hK0⟩ := (S.gam_vec hs).2
  let Wm : Set (Multiplicative (ElemGroup m' n' r' s' d')) := Multiplicative.toAdd ⁻¹' W
  have hWm : Wm ∈ 𝓝 (1 : Multiplicative (ElemGroup m' n' r' s' d')) :=
    continuous_toAdd.continuousAt.preimage_mem_nhds (by simpa using hW)
  have h1 : π ⁻¹' Wm ∈ 𝓝 (1 : Γ) := hπ.2.1.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hWm)
  rw [nhds_subtype, Filter.mem_comap] at h1
  obtain ⟨O, hO, hOW⟩ := h1
  have h2 : (fun y : B => S.emb 0 y) ⁻¹' O ∈ 𝓝 (0 : B) :=
    (S.cont_emb.comp (continuous_const.prodMk continuous_id)).continuousAt.preimage_mem_nhds
      (by show O ∈ 𝓝 (S.emb 0 0); rw [emb_zero]; simpa using hO)
  obtain ⟨M3, hM3⟩ := S.M_small _ (Filter.inter_mem h2 ((S.M_open K0).mem_nhds (zero_mem _)))
  refine ⟨M3, fun y hy => ?_⟩
  have hyΓ : S.emb 0 y ∈ Γ := hK0 y (hM3 hy).2
  have hj : ∀ j : ℕ, j • Multiplicative.toAdd (π ⟨S.emb 0 y, hyΓ⟩) ∈ W := by
    intro j
    have hjy : j • y ∈ S.M M3 := AddSubgroup.nsmul_mem _ hy j
    have hjΓ : S.emb 0 (j • y) ∈ Γ := hK0 _ (hM3 hjy).2
    have hmem : (⟨S.emb 0 (j • y), hjΓ⟩ : Γ) ∈ π ⁻¹' Wm := hOW (hM3 hjy).1
    have heq : (⟨S.emb 0 (j • y), hjΓ⟩ : Γ) = (⟨S.emb 0 y, hyΓ⟩ : Γ) ^ j := by
      apply Subtype.ext
      simp [emb_pow]
    rw [heq] at hmem
    have h3 : π (⟨S.emb 0 y, hyΓ⟩ ^ j) ∈ Wm := hmem
    rw [map_pow] at h3
    simpa [Wm, toAdd_pow] using h3
  have h0 := hWs _ hj
  have : π ⟨S.emb 0 y, hyΓ⟩ = 1 := by
    apply Multiplicative.toAdd.injective; rw [h0, toAdd_one]
  exact (hπ.2.2.2.2 _).1 this

/-- the classification of the structural pairs -/
lemma classify {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    {π : Γ →* Multiplicative (ElemGroup m' n' r' s' d')}
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    ∃ (Aₗ : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) (K : ℝ), 0 ≤ K ∧ (∀ x, ‖x‖ ≤ K * ‖Aₗ x‖) ∧
      (∀ x y (h : S.emb x y ∈ Γ) (h0 : S.emb 0 y ∈ Γ), Multiplicative.toAdd (π ⟨S.emb x y, h⟩) =
        (Aₗ x, 0, 0, 0) + Multiplicative.toAdd (π ⟨S.emb 0 y, h0⟩)) ∧
      (∃ M, (∀ z ∈ Γ, S.Y z ∈ S.L M) ∧ ∀ y ∈ S.M M, S.emb 0 y ∈ k) := by
  have hv := (S.gam_vec hs).1
  have hk := hs.2.2.1.2.1
  obtain ⟨M1, hM1⟩ := S.gam_bound hs
  obtain ⟨M3, hM3⟩ := S.kk_sub hs hπ
  -- the map on the vector part
  let φ : (Fin m → ℝ) →+ ElemGroup m' n' r' s' d' :=
    { toFun := fun x => Multiplicative.toAdd (π ⟨S.emb x 0, hv x⟩)
      map_zero' := by
        have : (⟨S.emb 0 0, hv 0⟩ : Γ) = 1 := Subtype.ext (S.emb_zero)
        simp only [this, map_one, toAdd_one]
      map_add' := fun x x' => by
        have : (⟨S.emb (x + x') 0, hv (x + x')⟩ : Γ) = ⟨S.emb x 0, hv x⟩ * ⟨S.emb x' 0, hv x'⟩ :=
          Subtype.ext (by simp [emb_mul])
        simp only [this, map_mul, toAdd_mul] }
  have hφ : ∀ x, φ x = Multiplicative.toAdd (π ⟨S.emb x 0, hv x⟩) := fun _ => rfl
  have hφc : Continuous φ := continuous_toAdd.comp (hπ.2.1.comp
    ((S.cont_emb.comp (continuous_id.prodMk continuous_const)).subtype_mk _))
  have hφk : ∀ x, φ x = 0 → x = 0 := by
    intro x hx
    refine S.vec_ker hk x ((hπ.2.2.2.2 ⟨S.emb x 0, hv x⟩).1 ?_)
    apply Multiplicative.toAdd.injective; rw [toAdd_one]; exact hx
  -- the split formula
  have hsplit : ∀ x y (h : S.emb x y ∈ Γ) (h0 : S.emb 0 y ∈ Γ), Multiplicative.toAdd
      (π ⟨S.emb x y, h⟩) = φ x + Multiplicative.toAdd (π ⟨S.emb 0 y, h0⟩) := by
    intro x y h h0
    have : (⟨S.emb x y, h⟩ : Γ) = ⟨S.emb x 0, hv x⟩ * ⟨S.emb 0 y, h0⟩ :=
      Subtype.ext (by simp [emb_mul])
    rw [this, map_mul, toAdd_mul, hφ]
  -- the range of `φ` is a neighbourhood of `0`
  have hrange : Set.range φ ∈ 𝓝 (0 : ElemGroup m' n' r' s' d') := by
    let U : Set Γ := {z | S.Y z ∈ S.M M3}
    have hU : IsOpen U := ((S.M_open M3).preimage S.cont_Y).preimage continuous_subtype_val
    have hπU := hπ.2.2.1 U hU
    have h1 : (Multiplicative.ofAdd ⁻¹' (π '' U)) ∈ 𝓝 (0 : ElemGroup m' n' r' s' d') := by
      refine (hπU.preimage continuous_ofAdd).mem_nhds ?_
      refine ⟨1, ?_, by simp⟩
      show S.Y 1 ∈ S.M M3; rw [Y_one]; exact zero_mem _
    refine Filter.mem_of_superset h1 ?_
    rintro w ⟨z, hz, hzw⟩
    refine ⟨S.X z, ?_⟩
    have h0Γ : S.emb 0 (S.Y z) ∈ Γ := (S.emb_mem_iff hs (S.X z) (S.Y z)).1 (by rw [emb_XY]; exact z.2)
    have hz' : (z : Γ) = ⟨S.emb (S.X z) (S.Y z), by rw [emb_XY]; exact z.2⟩ :=
      Subtype.ext (S.emb_XY z).symm
    have hk0 : π ⟨S.emb 0 (S.Y z), h0Γ⟩ = 1 := (hπ.2.2.2.2 _).2 (hM3 _ hz)
    have := hsplit (S.X z) (S.Y z) (by rw [emb_XY]; exact z.2) h0Γ
    rw [hk0, toAdd_one, add_zero, ← hz'] at this
    rw [← this, hzw, toAdd_ofAdd]
  -- the torus part is trivial
  have hn' : n' = 0 := by
    by_contra hn'
    let c : ℝ → ElemGroup m' n' r' s' d' := fun t => (0, fun _ => ((t : ℝ) : UnitAddCircle), 0, 0)
    have hc : Continuous c := continuous_const.prodMk
      ((continuous_pi fun _ => continuous_quotient_mk'.comp continuous_id).prodMk continuous_const)
    have hc0 : c 0 = 0 := by
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      funext i; show (((0 : ℝ) : ℝ) : UnitAddCircle) = 0; simp
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ Set.range φ :=
      hc.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hrange)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨q, hq⟩ := exists_nat_gt (max 2 (1 / ε))
    have hq2 : (2 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq
    have hqpos : (0 : ℝ) < q := by linarith
    have hqε : 1 / (q : ℝ) < ε := by
      rw [div_lt_iff₀ hqpos]
      have := lt_of_le_of_lt (le_max_right _ _) hq
      rw [div_lt_iff₀ hε] at this; linarith
    have hmem : c (1 / q) ∈ Set.range φ := hball (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; exact hqε)
    obtain ⟨x0, hx0⟩ := hmem
    have hq0 : φ (q • x0) = 0 := by
      rw [map_nsmul, hx0]
      refine Prod.ext (by simp [c]) (Prod.ext ?_ (by simp [c]))
      funext i
      show q • (((1 / q : ℝ) : ℝ) : UnitAddCircle) = 0
      rw [← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div_cancel hqpos.ne']
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨1, by simp⟩
    have hx00 : q • x0 = 0 := hφk _ hq0
    have hx0z : x0 = 0 := by
      have : (q : ℝ) • x0 = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hx00
      exact (smul_eq_zero.1 this).resolve_left hqpos.ne'
    rw [hx0z, map_zero] at hx0
    have h1 := congrArg (fun w => w.2.1 ⟨0, Nat.pos_of_ne_zero hn'⟩) hx0
    simp only [c] at h1
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h1.symm
    rw [zsmul_eq_mul, mul_one] at hz
    have hz0 : (0 : ℝ) < z := by rw [hz]; positivity
    have hz1 : (z : ℝ) < 1 := by
      rw [hz, div_lt_one hqpos]; linarith
    have hz0' : (0 : ℤ) < z := by exact_mod_cast hz0
    have hz1' : z < (1 : ℤ) := by exact_mod_cast hz1
    omega
  -- the discrete parts are trivial
  let ψZ : (Fin m → ℝ) →+ (Fin r' → ℤ) :=
    { toFun := fun x => (φ x).2.2.1, map_zero' := by simp, map_add' := fun x y => by simp }
  let ψF : (Fin m → ℝ) →+ ((i : Fin s') → ZMod (d' i)) :=
    { toFun := fun x => (φ x).2.2.2, map_zero' := by simp, map_add' := fun x y => by simp }
  have hZ := disc_zero ψZ ((continuous_fst.comp (continuous_snd.comp continuous_snd)).comp hφc)
  have hF := disc_zero ψF ((continuous_snd.comp (continuous_snd.comp continuous_snd)).comp hφc)
  let ψR : (Fin m → ℝ) →+ (Fin m' → ℝ) :=
    { toFun := fun x => (φ x).1, map_zero' := by simp, map_add' := fun x y => by simp }
  let Aₗ := ψR.toRealLinearMap (continuous_fst.comp hφc)
  have hAφ : ∀ x, φ x = (Aₗ x, 0, 0, 0) := by
    intro x
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext (hZ x) (hF x)))
    funext i; exact absurd i.2 (by omega)
  have hAinj : LinearMap.ker (Aₗ : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    refine hφk x ?_
    rw [hAφ]
    have : Aₗ x = 0 := hx
    rw [this]; rfl
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith _ hAinj
  refine ⟨Aₗ, K, K.2, fun x => ?_, fun x y h h0 => by rw [hsplit, hAφ], ?_⟩
  · have := hK.le_mul_dist x 0
    simpa using this
  · refine ⟨max M1 M3, fun z hz => S.L_mono (le_max_left _ _) (hM1 z hz), fun y hy => ?_⟩
    exact hM3 y (S.M_anti (le_max_right _ _) hy)

end Setup

end

end Aux_LFA

namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set

noncomputable section

namespace Setup

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {m : ℕ}
  (S : Setup A B m)

lemma sec_eq (N : ℕ) (q : ElemGroup m 0 0 (S.sN N) (S.dN N)) :
    S.sec N q = S.emb q.1 (S.rep N q.2.2.2) := rfl

open Classical in
lemma pull_eq {Γ k : Subgroup (Multiplicative A)} {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    {π : Γ →* Multiplicative (ElemGroup m' n' r' s' d')}
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (N : ℕ) :
    ∃ (Aₗ : (Fin m → ℝ) →L[ℝ] (Fin m' → ℝ)) (K : ℝ) (hK0 : 0 ≤ K)
      (hK : ∀ x, ‖x‖ ≤ K * ‖Aₗ x‖)
      (P : ((i : Fin (S.sN N)) → ZMod (S.dN N i)) → Prop)
      (c : ((i : Fin (S.sN N)) → ZMod (S.dN N i)) → ElemGroup m' n' r' s' d'),
      ∀ (g : ElemGroup m' n' r' s' d' → ℂ) q,
        extendPullback Γ π g (S.sec N q) = pbFun Aₗ P c g q := by
  obtain ⟨Aₗ, K, hK0, hK, hsplit, -⟩ := S.classify hs hπ
  refine ⟨Aₗ, K, hK0, hK, fun b => S.emb 0 (S.rep N b) ∈ Γ,
    fun b => if h : S.emb 0 (S.rep N b) ∈ Γ then Multiplicative.toAdd (π ⟨_, h⟩) else 0,
    fun g q => ?_⟩
  rw [sec_eq]
  unfold extendPullback pbFun
  by_cases hP : S.emb 0 (S.rep N q.2.2.2) ∈ Γ
  · have h : S.emb q.1 (S.rep N q.2.2.2) ∈ Γ := (S.emb_mem_iff hs _ _).2 hP
    rw [dif_pos h, if_pos hP]
    beta_reduce
    rw [dif_pos hP, hsplit q.1 _ h hP]
  · have h : S.emb q.1 (S.rep N q.2.2.2) ∉ Γ := fun h => hP ((S.emb_mem_iff hs _ _).1 h)
    rw [dif_neg h, if_neg hP]

/-- the stage inclusion -/
def J (N : ℕ) : Aux_LF.ESp m (S.sN N) (S.dN N) →ₗ[ℂ] SchwartzBruhat (Multiplicative A) where
  toFun y := SchwartzBruhat.ofElem (S.Gam N) (S.Kk N) (S.pres N) (S.stage_sp N) (S.pres_isElem N) y
  map_add' f g := by
    apply Subtype.ext; funext z
    show extendPullback _ _ (f + g).toFun z = extendPullback _ _ f.toFun z + extendPullback _ _ g.toFun z
    unfold extendPullback
    split_ifs
    · rfl
    · simp
  map_smul' c f := by
    apply Subtype.ext; funext z
    show extendPullback _ _ (c • f).toFun z = c • extendPullback _ _ f.toFun z
    unfold extendPullback
    split_ifs
    · rfl
    · simp

lemma J_apply (N : ℕ) (y : Aux_LF.ESp m (S.sN N) (S.dN N)) (z : Multiplicative A) :
    (S.J N y).toFun z = extendPullback (S.Gam N) (S.pres N) y.toFun z := rfl

lemma Pmem (N : ℕ) (f : SchwartzBruhat (Multiplicative A)) :
    (fun q => f.toFun (S.sec N q)) ∈ elemSchwartzSubmodule m 0 0 (S.sN N) (S.dN N) := by
  have h := f.2
  change f.1 ∈ Submodule.span ℂ _ at h
  show (fun q => f.1 (S.sec N q)) ∈ _
  refine Submodule.span_induction (p := fun x _ =>
    (fun q => x (S.sec N q)) ∈ elemSchwartzSubmodule m 0 0 (S.sN N) (S.dN N)) ?_ ?_ ?_ ?_ h
  · rintro _ ⟨Γ, k, m', n', r', s', d', π, g, hs, hπ, rfl⟩
    haveI : ∀ i, NeZero (d' i) := fun i => ⟨hπ.1 i⟩
    obtain ⟨Aₗ, K, hK0, hK, P, c, hpe⟩ := S.pull_eq hs hπ N
    have : (fun q => extendPullback Γ π g.toFun (S.sec N q)) = pbFun Aₗ P c g.toFun :=
      funext fun q => hpe _ q
    rw [this]
    exact Submodule.subset_span (pb_rd Aₗ K hK0 hK P c g)
  · exact zero_mem _
  · intro x y _ _ hx hy; exact add_mem hx hy
  · intro a x _ hx; exact Submodule.smul_mem _ a hx

/-- the stage projection -/
def P (N : ℕ) : SchwartzBruhat (Multiplicative A) →ₗ[ℂ] Aux_LF.ESp m (S.sN N) (S.dN N) where
  toFun f := ⟨fun q => f.toFun (S.sec N q), S.Pmem N f⟩
  map_add' f g := rfl
  map_smul' c f := rfl

lemma P_apply (N : ℕ) (f : SchwartzBruhat (Multiplicative A)) (q) :
    (S.P N f).toFun q = f.toFun (S.sec N q) := rfl

lemma cont_P_ofElem {Γ k : Subgroup (Multiplicative A)} {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    (π : Γ →* Multiplicative (ElemGroup m' n' r' s' d'))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (N : ℕ) :
    Continuous (fun g => S.P N (SchwartzBruhat.ofElem Γ k π hs hπ g)) := by
  haveI : ∀ i, NeZero (d' i) := fun i => ⟨hπ.1 i⟩
  obtain ⟨Aₗ, K, hK0, hK, Pp, c, hpe⟩ := S.pull_eq hs hπ N
  have : (fun g => S.P N (SchwartzBruhat.ofElem Γ k π hs hπ g)) =
      pbLin (d := S.dN N) Aₗ K hK0 hK Pp c := by
    funext g
    apply Subtype.ext
    funext q
    exact hpe g.toFun q
  rw [this]
  exact pbLin_cont _ _ _ _ _ _

/-- support and invariance at level `N` -/
def Good (N : ℕ) (h : Multiplicative A → ℂ) : Prop :=
  (∀ z, S.Y z ∉ S.L N → h z = 0) ∧ ∀ x y y', y' - y ∈ S.M N → h (S.emb x y) = h (S.emb x y')

lemma good_mono {N M : ℕ} (hNM : N ≤ M) {h : Multiplicative A → ℂ} (hh : S.Good N h) :
    S.Good M h :=
  ⟨fun z hz => hh.1 z fun h' => hz (S.L_mono hNM h'),
    fun x y y' hy => hh.2 x y y' (S.M_anti hNM hy)⟩

lemma JP_id (M : ℕ) (f : SchwartzBruhat (Multiplicative A)) (hf : S.Good M f.toFun) :
    S.J M (S.P M f) = f := by
  apply Subtype.ext
  funext z
  show (S.J M (S.P M f)).toFun z = f.toFun z
  rw [J_apply]
  unfold extendPullback
  split_ifs with hz
  · rw [P_apply, sec_eq, pres_apply]
    simp only
    conv_rhs => rw [← S.emb_XY z]
    refine (hf.2 _ _ _ ?_).symm
    have := (S.del_eq_iff M ⟨S.rep M (S.del M ⟨S.Y z, hz⟩), S.rep_mem M _⟩ ⟨S.Y z, hz⟩).1
      (S.del_rep M _)
    have h2 := neg_mem this
    simpa using h2
  · exact (hf.1 z hz).symm

lemma good_J (N : ℕ) (y : Aux_LF.ESp m (S.sN N) (S.dN N)) : S.Good N (S.J N y).toFun := by
  refine ⟨fun z hz => ?_, fun x a a' ha => ?_⟩
  · rw [J_apply]; unfold extendPullback; rw [dif_neg (show z ∉ S.Gam N from hz)]
  · rw [J_apply, J_apply]
    unfold extendPullback
    have hiff : S.emb x a ∈ S.Gam N ↔ S.emb x a' ∈ S.Gam N := by
      rw [mem_Gam, mem_Gam, Y_emb, Y_emb]
      constructor
      · intro h; have := add_mem h (S.ML N ha); simpa using this
      · intro h; have := sub_mem h (S.ML N ha); simpa using this
    by_cases h : S.emb x a ∈ S.Gam N
    · rw [dif_pos h, dif_pos (hiff.1 h)]
      congr 1
      rw [pres_apply, pres_apply]
      simp only [X_emb]
      congr 1
      refine congrArg (fun p => (0, 0, p)) ?_
      rw [S.del_eq_iff]
      simpa using ha
    · rw [dif_neg h, dif_neg (fun h' => h (hiff.2 h'))]

lemma good_ofElem {Γ k : Subgroup (Multiplicative A)} {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    (π : Γ →* Multiplicative (ElemGroup m' n' r' s' d'))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    ∃ M, ∀ g : ElemGroup m' n' r' s' d' → ℂ, S.Good M (extendPullback Γ π g) := by
  obtain ⟨-, -, -, -, -, M, hM1, hM2⟩ := S.classify hs hπ
  refine ⟨M, fun g => ⟨fun z hz => ?_, fun x a a' ha => ?_⟩⟩
  · unfold extendPullback
    rw [dif_neg (fun h => hz (hM1 z h))]
  · unfold extendPullback
    have hk : S.emb 0 (a' - a) ∈ k := hM2 _ ha
    have hkΓ : S.emb 0 (a' - a) ∈ Γ := hs.2.2.2 hk
    have heq : S.emb x a' = S.emb x a * S.emb 0 (a' - a) := by
      rw [emb_mul]; simp
    by_cases h : S.emb x a ∈ Γ
    · have h' : S.emb x a' ∈ Γ := by rw [heq]; exact mul_mem h hkΓ
      rw [dif_pos h, dif_pos h']
      congr 2
      have : (⟨S.emb x a', h'⟩ : Γ) = ⟨S.emb x a, h⟩ * ⟨S.emb 0 (a' - a), hkΓ⟩ :=
        Subtype.ext heq
      rw [this, map_mul, (hπ.2.2.2.2 ⟨S.emb 0 (a' - a), hkΓ⟩).2 hk, mul_one]
    · have h' : S.emb x a' ∉ Γ := by
        intro h'
        apply h
        have : S.emb x a = S.emb x a' * (S.emb 0 (a' - a))⁻¹ := by rw [heq]; group
        rw [this]; exact mul_mem h' (inv_mem hkΓ)
      rw [dif_neg h, dif_neg h']

lemma good_zero (N : ℕ) : S.Good N (0 : Multiplicative A → ℂ) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

lemma good_add {N : ℕ} {f g : Multiplicative A → ℂ} (hf : S.Good N f) (hg : S.Good N g) :
    S.Good N (f + g) :=
  ⟨fun z hz => by simp [hf.1 z hz, hg.1 z hz],
    fun x y y' h => by simp [hf.2 x y y' h, hg.2 x y y' h]⟩

lemma good_smul {N : ℕ} (c : ℂ) {f : Multiplicative A → ℂ} (hf : S.Good N f) :
    S.Good N (c • f) :=
  ⟨fun z hz => by simp [hf.1 z hz], fun x y y' h => by simp [hf.2 x y y' h]⟩

lemma exists_good (f : SchwartzBruhat (Multiplicative A)) : ∃ N, S.Good N f.toFun := by
  have h := f.2
  change f.1 ∈ Submodule.span ℂ _ at h
  show ∃ N, S.Good N f.1
  refine Submodule.span_induction (p := fun x _ => ∃ N, S.Good N x) ?_ ⟨0, S.good_zero 0⟩ ?_ ?_ h
  · rintro _ ⟨Γ, k, m', n', r', s', d', π, g, hs, hπ, rfl⟩
    obtain ⟨M, hM⟩ := S.good_ofElem π hs hπ
    exact ⟨M, hM _⟩
  · rintro x y _ _ ⟨N, hN⟩ ⟨M, hM⟩
    exact ⟨max N M, S.good_add (S.good_mono (le_max_left _ _) hN)
      (S.good_mono (le_max_right _ _) hM)⟩
  · rintro c x _ ⟨N, hN⟩
    exact ⟨N, S.good_smul c hN⟩

lemma PJ (N : ℕ) (y : Aux_LF.ESp m (S.sN N) (S.dN N)) : S.P N (S.J N y) = y := by
  apply Subtype.ext
  funext q
  show (S.J N y).toFun (S.sec N q) = y.toFun q
  rw [J_apply]
  unfold extendPullback
  rw [dif_pos (S.sec_mem N q), pres_sec]

lemma P_anti {N M : ℕ} (h : N ≤ M) (f : SchwartzBruhat (Multiplicative A)) :
    S.P N (S.J M (S.P M f)) = S.P N f := by
  apply Subtype.ext
  funext q
  show (S.J M (S.P M f)).toFun (S.sec N q) = f.toFun (S.sec N q)
  rw [J_apply]
  unfold extendPullback
  have hmem : S.sec N q ∈ S.Gam M := by
    show S.Y _ ∈ S.L M; rw [sec_eq, Y_emb]; exact S.L_mono h (S.rep_mem N _)
  rw [dif_pos hmem, P_apply]
  have hy : (⟨S.Y (S.sec N q), hmem⟩ : ↥(S.L M)) = ⟨S.rep N q.2.2.2, S.L_mono h (S.rep_mem N _)⟩ :=
    Subtype.ext (by show S.Y (S.sec N q) = S.rep N q.2.2.2; rw [sec_eq, Y_emb])
  have key : S.sec M (Multiplicative.toAdd (S.pres M ⟨S.sec N q, hmem⟩)) = S.sec N q := by
    rw [pres_apply]
    show S.emb (S.X (S.sec N q)) (S.rep M (S.del M ⟨S.Y (S.sec N q), hmem⟩)) = _
    rw [hy, S.rep_nested h, sec_eq, X_emb]
  rw [key]

include S in
theorem sbdata : ∃ D : Aux_LF.SBData (Multiplicative A), ∀ N, D.m N = m := by
  refine ⟨{
    m := (fun _ => m)
    s := S.sN
    d := S.dN
    hd := S.hdN
    J := S.J
    P := S.P
    PJ := S.PJ
    JP_mono := ?_
    JP_anti := ?_
    exh := ?_
    J_eq := ?_
    stage := ?_
    PJ_cont := ?_ }, fun _ => rfl⟩
  · intro N M f h
    exact S.JP_id M _ (S.good_mono h (S.good_J N _))
  · intro N M f h
    rw [S.P_anti h]
  · intro f
    obtain ⟨N, hN⟩ := S.exists_good f
    exact ⟨N, S.JP_id N f hN⟩
  · intro N
    exact ⟨S.Gam N, S.Kk N, S.pres N, S.stage_sp N, S.pres_isElem N, fun y => rfl⟩
  · intro Γ k m' n' r' s' d' π hs hπ
    obtain ⟨M, hM⟩ := S.good_ofElem π hs hπ
    exact ⟨M, fun g => S.JP_id M _ (hM _), S.cont_P_ofElem π hs hπ M⟩
  · intro N M
    exact S.cont_P_ofElem (S.pres M) (S.stage_sp M) (S.pres_isElem M) N

end Setup

end

end Aux_LFA

namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set NumberField IsDedekindDomain

noncomputable section

/-! ### building the filtration from a compact open subring -/

section ringb

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- data: a compact open subring `O` with `B = ⋃ (N!)⁻¹ O` and `⋂ N! O = 0` -/
structure RingData (B : Type*) [CommRing B] [TopologicalSpace B] where
  O : Subring B
  O_open : IsOpen (O : Set B)
  O_cpt : IsCompact (O : Set B)
  unit : ∀ N : ℕ, IsUnit ((N.factorial : ℕ) : B)
  cov : ∀ x : B, ∃ N : ℕ, ((N.factorial : ℕ) : B) * x ∈ O
  inter : ∀ x : B, (∀ N : ℕ, ∃ y ∈ O, x = ((N.factorial : ℕ) : B) * y) → x = 0

namespace RingData

variable (R : RingData B)

/-- `N!` -/
abbrev c (N : ℕ) : B := ((N.factorial : ℕ) : B)
/-- `(N!)⁻¹` -/
def ci (N : ℕ) : B := ↑((R.unit N).unit⁻¹)
lemma ci_c (N : ℕ) : R.ci N * c N = 1 := (R.unit N).val_inv_mul
lemma c_ci (N : ℕ) : c N * R.ci N = 1 := (R.unit N).mul_val_inv

/-- `L_N = (N!)⁻¹ O` -/
def L (N : ℕ) : AddSubgroup B := R.O.toAddSubgroup.comap (AddMonoidHom.mulLeft (c N))
/-- `M_N = N! O` -/
def M (N : ℕ) : AddSubgroup B := R.O.toAddSubgroup.comap (AddMonoidHom.mulLeft (R.ci N))

lemma mem_L {N x} : x ∈ R.L N ↔ c N * x ∈ R.O := Iff.rfl
lemma mem_M {N x} : x ∈ R.M N ↔ R.ci N * x ∈ R.O := Iff.rfl

lemma mem_M' {N x} : x ∈ R.M N ↔ ∃ y ∈ R.O, x = c N * y := by
  rw [mem_M]
  constructor
  · intro h; refine ⟨_, h, ?_⟩; rw [← mul_assoc, R.c_ci, one_mul]
  · rintro ⟨y, hy, rfl⟩; rwa [← mul_assoc, R.ci_c, one_mul]

lemma L_eq (N : ℕ) : (R.L N : Set B) = (fun y => R.ci N * y) '' (R.O : Set B) := by
  ext x
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    show R.ci N * (c N * x) = x
    rw [← mul_assoc, R.ci_c, one_mul]
  · rintro ⟨y, hy, rfl⟩
    show c N * (R.ci N * y) ∈ R.O
    rwa [← mul_assoc, R.c_ci, one_mul]

lemma M_eq (N : ℕ) : (R.M N : Set B) = (fun y => c N * y) '' (R.O : Set B) := by
  ext x
  rw [SetLike.mem_coe, mem_M']
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

lemma nat_mem (n : ℕ) : (n : B) ∈ R.O := natCast_mem _ n

lemma fact_dvd {N N' : ℕ} (h : N ≤ N') : ∃ t : ℕ, c N' = (t : B) * c N := by
  obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial h
  exact ⟨t, by simp only [c]; rw [ht]; push_cast; ring⟩

lemma M_inter (x : B) (hx : x ∈ ⋂ N, (R.M N : Set B)) : x = 0 :=
  R.inter x fun N => (R.mem_M').1 (mem_iInter.1 hx N)

end RingData

/-- the `Setup` attached to a `RingData` -/
def ringSetup {A : Type*} [AddCommGroup A] [TopologicalSpace A] {m : ℕ} (R : RingData B)
    (e : ((Fin m → ℝ) × B) ≃+ A) (he : Continuous e) (hes : Continuous e.symm) : Setup A B m where
  e := e
  he := he
  hes := hes
  L := R.L
  M := R.M
  L_open N := R.O_open.preimage (continuous_mul_left (RingData.c N : B))
  L_cpt N := by rw [R.L_eq]; exact R.O_cpt.image (continuous_mul_left (R.ci N))
  M_open N := R.O_open.preimage (continuous_mul_left (R.ci N))
  M_cpt N := by rw [R.M_eq]; exact R.O_cpt.image (continuous_mul_left (RingData.c N : B))
  L_mono N N' h x hx := by
    obtain ⟨t, ht⟩ := RingData.fact_dvd (B := B) h
    show RingData.c N' * x ∈ R.O
    rw [ht, mul_assoc]; exact mul_mem (R.nat_mem t) hx
  M_anti N N' h x hx := by
    obtain ⟨y, hy, rfl⟩ := (R.mem_M').1 hx
    obtain ⟨t, ht⟩ := RingData.fact_dvd (B := B) h
    refine (R.mem_M').2 ⟨t * y, mul_mem (R.nat_mem t) hy, ?_⟩
    rw [ht]; ring
  ML N x hx := by
    obtain ⟨y, hy, rfl⟩ := (R.mem_M').1 hx
    show RingData.c N * (RingData.c N * y) ∈ R.O
    exact mul_mem (R.nat_mem _) (mul_mem (R.nat_mem _) hy)
  L_cov x := R.cov x
  M_small W hW := by
    have hdir : Directed (· ⊇ ·) (fun N => (R.M N : Set B)) := by
      intro a b
      refine ⟨max a b, ?_, ?_⟩
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := (R.mem_M').1 hx
        obtain ⟨t, ht⟩ := RingData.fact_dvd (B := B) (le_max_left a b)
        exact (R.mem_M').2 ⟨t * y, mul_mem (R.nat_mem t) hy, by rw [ht]; ring⟩
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := (R.mem_M').1 hx
        obtain ⟨t, ht⟩ := RingData.fact_dvd (B := B) (le_max_right a b)
        exact (R.mem_M').2 ⟨t * y, mul_mem (R.nat_mem t) hy, by rw [ht]; ring⟩
    exact exists_subset_nhds_of_isCompact' hdir
      (fun N => by rw [R.M_eq]; exact R.O_cpt.image (continuous_mul_left (RingData.c N : B)))
      (fun N => AddSubgroup.isClosed_of_isOpen _ (R.O_open.preimage (continuous_mul_left (R.ci N))))
      (fun x hx => by rw [R.M_inter x hx]; exact hW)

end ringb

/-! ### the local fields -/

section local_

open IsLocalRing
open scoped WithZero

variable {F : Type*} [Field F] [NumberField F]

theorem nonempty_residueFieldEquiv (v : HeightOneSpectrum (𝓞 F)) :
    Nonempty ((𝓞 F ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  let O := v.adicCompletionIntegers F
  let f := (residue O).comp (algebraMap (𝓞 F) O)
  let q : 𝓞 F ⧸ v.asIdeal →+* ResidueField O := Ideal.Quotient.lift v.asIdeal f (by
    intro r hr
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).2
    change Valued.v ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.valuation_lt_one_iff_mem r).2 hr)
  let := Ideal.Quotient.field v.asIdeal
  refine ⟨RingEquiv.ofBijective q ⟨q.injective, ?_⟩⟩
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  let ν : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have hn : {z | ν (z - (x : v.adicCompletion F)) < 1} ∈ 𝓝 (x : v.adicCompletion F) := by
    refine Valued.mem_nhds.mpr ⟨1, ?_⟩
    intro z hz
    simpa only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_iff_lt_embedding,
      map_one] using hz
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap F).mem_nhds hn
  change ν (algebraMap F (v.adicCompletion F) a - x) < 1 at ha
  have ha' : v.valuation F a ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change ν (algebraMap F (v.adicCompletion F) a) ≤ 1
    simpa only [sub_add_cancel] using ν.map_add_le ha.le x.property
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer ha' 1
  have hr' : ν (algebraMap (𝓞 F) (v.adicCompletion F) r -
      algebraMap F (v.adicCompletion F) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub]
    change Valued.v (((algebraMap (𝓞 F) F) r - a : F) : v.adicCompletion F) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [Units.val_one] using hr
  refine ⟨Ideal.Quotient.mk _ r, sub_eq_zero.mp ?_⟩
  change residue O (algebraMap (𝓞 F) O r) - residue O x = 0
  rw [← map_sub, residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff _ ν).2
  change ν (algebraMap (𝓞 F) (v.adicCompletion F) r - x) < 1
  simpa only [sub_add_sub_cancel] using ν.map_add_lt hr' ha

theorem finite_residueField (v : HeightOneSpectrum (𝓞 F)) :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  obtain ⟨e⟩ := nonempty_residueFieldEquiv v
  have : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  exact Finite.of_equiv _ e.toEquiv

theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) := by
  have : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isClosed_valuationSubring _
  have hcomplete : CompleteSpace (v.adicCompletionIntegers F) := IsClosed.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hcomplete, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
      finite_residueField v⟩

theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have := compactSpace_adicCompletionIntegers v
  exact isCompact_iff_compactSpace.mpr this

theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_valuationSubring _

lemma natc (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ((n : ℕ) : v.adicCompletion F) = (((n : ℕ) : F) : v.adicCompletion F) := by
  induction n with
  | zero => rw [Nat.cast_zero, Nat.cast_zero, HeightOneSpectrum.adicCompletion.coe_zero]
  | succ n ih => rw [Nat.cast_succ, Nat.cast_succ, ih, HeightOneSpectrum.adicCompletion.coe_add, HeightOneSpectrum.adicCompletion.coe_one]

lemma norm_nat_le (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : ‖((n : ℕ) : v.adicCompletion F)‖ ≤ 1 := by
  refine (Valued.toNormedField.norm_le_one_iff).2 ?_
  rw [natc, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have := v.valuation_le_one (K := F) (n : 𝓞 F)
  simpa using this

lemma norm_absNorm_lt (v : HeightOneSpectrum (𝓞 F)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ < 1 := by
  refine (Valued.toNormedField.norm_lt_one_iff).2 ?_
  rw [natc, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have := (v.valuation_lt_one_iff_mem (K := F) ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2
    (Ideal.absNorm_mem v.asIdeal)
  simpa using this

lemma fact_small (v : HeightOneSpectrum (𝓞 F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ‖((N.factorial : ℕ) : v.adicCompletion F)‖ < ε := by
  set nn := Ideal.absNorm v.asIdeal
  have hq := norm_absNorm_lt v
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hq
  have hnn : nn ≠ 0 := by
    intro h; exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨nn ^ k, fun N hN => ?_⟩
  obtain ⟨t, ht⟩ := Nat.dvd_factorial (pow_pos (Nat.pos_of_ne_zero hnn) k) hN
  rw [ht]
  push_cast
  rw [norm_mul, norm_pow]
  calc ‖(nn : v.adicCompletion F)‖ ^ k * ‖(t : v.adicCompletion F)‖
      ≤ ‖(nn : v.adicCompletion F)‖ ^ k * 1 :=
        mul_le_mul_of_nonneg_left (norm_nat_le v t) (by positivity)
    _ < ε := by rw [mul_one]; exact hk

lemma mem_O_iff (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    x ∈ v.adicCompletionIntegers F ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (Valued.toNormedField.norm_le_one_iff).symm

lemma loc_cov (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ((N.factorial : ℕ) : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F := by
  by_cases hx : x = 0
  · exact ⟨0, fun N _ => by rw [hx, mul_zero]; exact zero_mem _⟩
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨N0, hN0⟩ := fact_small v (1 / ‖x‖) (by positivity)
  refine ⟨N0, fun N hN => (mem_O_iff v _).2 ?_⟩
  rw [norm_mul]
  have := hN0 N hN
  rw [lt_div_iff₀ hpos] at this
  exact this.le

lemma loc_inter (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : ∀ N : ℕ, ∃ y ∈ v.adicCompletionIntegers F, x = ((N.factorial : ℕ) : v.adicCompletion F) * y) :
    x = 0 := by
  by_contra hx
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨N0, hN0⟩ := fact_small v ‖x‖ hpos
  obtain ⟨y, hy, hxy⟩ := h N0
  have h1 := hN0 N0 le_rfl
  have h2 : ‖x‖ ≤ ‖((N0.factorial : ℕ) : v.adicCompletion F)‖ := by
    rw [hxy, norm_mul]
    calc _ ≤ ‖((N0.factorial : ℕ) : v.adicCompletion F)‖ * 1 :=
          mul_le_mul_of_nonneg_left ((mem_O_iff v y).1 hy) (norm_nonneg _)
      _ = _ := mul_one _
  linarith

end local_

end

end Aux_LFA

namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set NumberField IsDedekindDomain

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

lemma fact_ne (N : ℕ) : ((N.factorial : ℕ) : F) ≠ 0 :=
  Nat.cast_ne_zero.2 (Nat.factorial_ne_zero N)

/-! ### the finite adeles -/

lemma fin_nat_apply (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    ((n : ℕ) : FiniteAdeleRing (𝓞 F) F) v = ((n : ℕ) : v.adicCompletion F) := by
  rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), FiniteAdeleRing.algebraMap_apply,
    natc]

/-- the integral finite adeles -/
def finO : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  mul_mem' {x y} hx hy v := by
    show x v * y v ∈ _
    exact mul_mem (hx v) (hy v)
  one_mem' v := by
    show (1 : v.adicCompletion F) ∈ _
    exact one_mem _
  add_mem' {x y} hx hy v := by
    show x v + y v ∈ _
    exact add_mem (hx v) (hy v)
  zero_mem' v := by
    show (0 : v.adicCompletion F) ∈ _
    exact zero_mem _
  neg_mem' {x} hx v := by
    show -x v ∈ _
    exact neg_mem (hx v)

lemma finO_open : IsOpen (finO F : Set (FiniteAdeleRing (𝓞 F) F)) :=
  RestrictedProduct.isOpen_forall_mem (fun v => isOpen_adicCompletionIntegers v)

lemma finO_cpt : IsCompact (finO F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) :=
    fun v => compactSpace_adicCompletionIntegers v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap (R := fun v :
    HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F :
    Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

/-- the ring data of the finite adeles -/
def finRD : RingData (FiniteAdeleRing (𝓞 F) F) where
  O := finO F
  O_open := finO_open F
  O_cpt := finO_cpt F
  unit N := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F))]
    exact (Ne.isUnit (fact_ne F N)).map _
  cov x := by
    classical
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ x v ∈ v.adicCompletionIntegers F}.Finite :=
      Filter.eventually_cofinite.1 x.2
    choose Nv hNv using fun v : HeightOneSpectrum (𝓞 F) => loc_cov v (x v)
    refine ⟨hfin.toFinset.sup Nv, fun v => ?_⟩
    show ((((hfin.toFinset.sup Nv).factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) v) * x v ∈ _
    rw [fin_nat_apply]
    by_cases hv : x v ∈ v.adicCompletionIntegers F
    · exact mul_mem (natCast_mem _ _) hv
    · exact hNv v _ (Finset.le_sup (f := Nv) (hfin.mem_toFinset.2 hv))
  inter x hx := by
    refine FiniteAdeleRing.ext F fun v => ?_
    refine (loc_inter v (x v) fun N => ?_).trans rfl
    obtain ⟨y, hy, rfl⟩ := hx N
    refine ⟨y v, hy v, ?_⟩
    show ((((N.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) v) * y v = _
    rw [fin_nat_apply]

/-! ### the finite part of the `S`-adeles -/

/-- the integral elements of `∏_{v ∈ S_f} F_v` -/
def sO (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    Subring ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :=
  { carrier := {x | ∀ v : Sf, x v ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F}
    mul_mem' := fun hx hy v => mul_mem (hx v) (hy v)
    one_mem' := fun v => one_mem _
    add_mem' := fun hx hy v => add_mem (hx v) (hy v)
    zero_mem' := fun v => zero_mem _
    neg_mem' := fun hx v => neg_mem (hx v) }

lemma mem_sO (Sf : Finset (HeightOneSpectrum (𝓞 F))) (x) :
    x ∈ sO F Sf ↔ ∀ v : Sf, x v ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
  Iff.rfl

/-- the ring data of `∏_{v ∈ S_f} F_v` -/
def sRD (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    RingData ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) where
  O := sO F Sf
  O_open := by
    have : (sO F Sf : Set ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) =
        Set.pi (Set.univ : Set Sf) fun v => ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :
          Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) := by
      ext x; simp [mem_sO]
    rw [this]
    exact isOpen_set_pi Set.finite_univ fun v _ => isOpen_adicCompletionIntegers _
  O_cpt := by
    have : (sO F Sf : Set ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) =
        Set.pi (Set.univ : Set Sf) fun v => ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :
          Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) := by
      ext x; simp [mem_sO]
    rw [this]
    exact isCompact_univ_pi fun v => isCompact_adicCompletionIntegers _
  unit N := by
    rw [Pi.isUnit_iff]
    intro v
    rw [Pi.natCast_apply, ← map_natCast (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))]
    exact (Ne.isUnit (fact_ne F N)).map _
  cov x := by
    classical
    choose Nv hNv using fun v : Sf => loc_cov (v : HeightOneSpectrum (𝓞 F)) (x v)
    refine ⟨Finset.univ.sup Nv, (mem_sO F Sf _).2 fun v => ?_⟩
    rw [Pi.mul_apply, Pi.natCast_apply]
    exact hNv v _ (Finset.le_sup (f := Nv) (Finset.mem_univ v))
  inter x hx := by
    funext v
    refine loc_inter (v : HeightOneSpectrum (𝓞 F)) (x v) fun N => ?_
    obtain ⟨y, hy, rfl⟩ := hx N
    exact ⟨y v, (mem_sO F Sf y).1 hy v, by rw [Pi.mul_apply, Pi.natCast_apply]⟩

/-! ### the infinite adeles as a real vector space -/

lemma cont_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = fun x =>
      ((fun (v : {w : InfinitePlace F // InfinitePlace.IsReal w}) =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // InfinitePlace.IsComplex w}) =>
        InfinitePlace.Completion.extensionEmbedding v.1 (x v))) :=
    funext (InfiniteAdeleRing.ringEquiv_mixedSpace_apply F)
  rw [this]
  refine (continuous_pi fun v => ?_).prodMk (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

lemma cont_mixed_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  set g := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
  have hg : ∀ y, InfiniteAdeleRing.ringEquiv_mixedSpace F (g y) = y := fun y =>
    RingEquiv.apply_symm_apply _ y
  refine continuous_pi fun w => ?_
  by_cases hw : InfinitePlace.IsReal w
  · have hi := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).isUniformInducing.isInducing
    refine hi.continuous_iff.2 ?_
    have : (⇑(InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) ∘ fun y => g y w) =
        fun y => y.1 ⟨w, hw⟩ := by
      funext y
      have := congrArg (fun p => p.1 ⟨w, hw⟩) (hg y)
      simpa using this
    rw [this]; exact (continuous_apply _).comp continuous_fst
  · have hc : InfinitePlace.IsComplex w := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have hi := (InfinitePlace.Completion.isometry_extensionEmbedding w).isUniformInducing.isInducing
    refine hi.continuous_iff.2 ?_
    have : (⇑(InfinitePlace.Completion.extensionEmbedding w) ∘ fun y => g y w) =
        fun y => y.2 ⟨w, hc⟩ := by
      funext y
      have := congrArg (fun p => p.2 ⟨w, hc⟩) (hg y)
      simpa using this
    rw [this]; exact (continuous_apply _).comp continuous_snd

/-- the real dimension -/
abbrev dimV : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)

/-- `mixedSpace ≅ ℝ^d` -/
def linV : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (Fin (dimV F) → ℝ) :=
  LinearEquiv.ofFinrankEq _ _ (by simp)

/-- `K_∞ ≅ ℝ^d` -/
def eV : InfiniteAdeleRing F ≃+ (Fin (dimV F) → ℝ) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv.trans (linV F).toAddEquiv

lemma cont_eV : Continuous (eV F) :=
  (LinearMap.continuous_of_finiteDimensional (linV F).toLinearMap).comp (cont_mixed F)

lemma cont_eV_symm : Continuous (eV F).symm :=
  (cont_mixed_symm F).comp (LinearMap.continuous_of_finiteDimensional (linV F).symm.toLinearMap)

/-- `ℝ^0 × B ≅ B` -/
def e0 (B : Type*) [AddCommGroup B] : ((Fin 0 → ℝ) × B) ≃+ B where
  toFun p := p.2
  invFun y := (0, y)
  left_inv p := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv y := rfl
  map_add' _ _ := rfl

end

end Aux_LFA

namespace Aux_LF

open MasulloGRH NumberField IsDedekindDomain Aux_LFA

theorem sbdata_finadeles (F : Type*) [Field F] [NumberField F] :
    ∃ D : Aux_LF.SBData (Multiplicative (FiniteAdeleRing (𝓞 F) F)), ∀ N, D.m N = 0 :=
  (ringSetup (finRD F) (e0 _) continuous_snd (continuous_const.prodMk continuous_id)).sbdata

theorem sbdata_adeles (F : Type*) [Field F] [NumberField F] :
    Nonempty (Aux_LF.SBData (Multiplicative (AdeleRing (𝓞 F) F))) := by
  haveI : IsTopologicalAddGroup (AdeleRing (𝓞 F) F) :=
    inferInstanceAs (IsTopologicalAddGroup (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  let e : ((Fin (dimV F) → ℝ) × FiniteAdeleRing (𝓞 F) F) ≃+ AdeleRing (𝓞 F) F :=
    AddEquiv.prodCongr (eV F).symm (AddEquiv.refl (FiniteAdeleRing (𝓞 F) F))
  have he : Continuous e := (cont_eV_symm F).prodMap continuous_id
  have hes : Continuous e.symm := (cont_eV F).prodMap continuous_id
  obtain ⟨D, -⟩ := (ringSetup (A := AdeleRing (𝓞 F) F) (finRD F) e he hes).sbdata
  exact ⟨D⟩

theorem sbdata_sadeles (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    Nonempty (Aux_LF.SBData (Multiplicative (SAdeleRing F Sf))) := by
  let e : ((Fin (dimV F) → ℝ) × ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) ≃+
      SAdeleRing F Sf :=
    AddEquiv.prodCongr (eV F).symm (AddEquiv.refl _)
  have he : Continuous e := (cont_eV_symm F).prodMap continuous_id
  have hes : Continuous e.symm := (cont_eV F).prodMap continuous_id
  obtain ⟨D, -⟩ := (ringSetup (sRD F Sf) e he hes).sbdata
  exact ⟨D⟩

end Aux_LF


namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set

noncomputable section

namespace Setup

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] {m : ℕ}
  (S : Setup A B m)

/-- the stage data as an explicit `SBData` -/
def toSBData : Aux_LF.SBData (Multiplicative A) where
  m := fun _ => m
  s := S.sN
  d := S.dN
  hd := S.hdN
  J := S.J
  P := S.P
  PJ := S.PJ
  JP_mono N M f h := S.JP_id M _ (S.good_mono h (S.good_J N _))
  JP_anti N M f h := by rw [S.P_anti h]
  exh f := by
    obtain ⟨N, hN⟩ := S.exists_good f
    exact ⟨N, S.JP_id N f hN⟩
  J_eq N := ⟨S.Gam N, S.Kk N, S.pres N, S.stage_sp N, S.pres_isElem N, fun y => rfl⟩
  stage Γ k m' n' r' s' d' π hs hπ := by
    obtain ⟨M, hM⟩ := S.good_ofElem π hs hπ
    exact ⟨M, fun g => S.JP_id M _ (hM _), S.cont_P_ofElem π hs hπ M⟩
  PJ_cont N M := S.cont_P_ofElem (S.pres M) (S.stage_sp M) (S.pres_isElem M) N

lemma toSBData_J (N : ℕ) : (S.toSBData).J N = S.J N := rfl

lemma ext_good (M : ℕ) (h : Multiplicative A → ℂ) (hh : S.Good M h) (z : Multiplicative A) :
    extendPullback (S.Gam M) (S.pres M) (fun q => h (S.sec M q)) z = h z := by
  unfold extendPullback
  split_ifs with hz
  · show h (S.sec M _) = h z
    rw [sec_eq, pres_apply]
    conv_rhs => rw [← S.emb_XY z]
    refine (hh.2 _ _ _ ?_).symm
    have := (S.del_eq_iff M ⟨S.rep M (S.del M ⟨S.Y z, hz⟩), S.rep_mem M _⟩ ⟨S.Y z, hz⟩).1
      (S.del_rep M _)
    have h2 := neg_mem this
    simpa using h2
  · exact (hh.1 z hz).symm

open Classical in
lemma ep_emb (N : ℕ) (y : Aux_LF.ESp m (S.sN N) (S.dN N)) (x : Fin m → ℝ) (a : B) :
    extendPullback (S.Gam N) (S.pres N) y.toFun (S.emb x a) =
      if h : a ∈ S.L N then y.toFun (x, 0, 0, S.del N ⟨a, h⟩) else 0 := by
  unfold extendPullback
  have hiff : S.emb x a ∈ S.Gam N ↔ a ∈ S.L N := by rw [mem_Gam, Y_emb]
  by_cases h : a ∈ S.L N
  · rw [dif_pos (hiff.2 h), dif_pos h, pres_apply]
    congr 1
    refine Prod.ext (by simp) (Prod.ext rfl (Prod.ext rfl ?_))
    show S.del N _ = S.del N _
    congr 1; apply Subtype.ext; simp
  · rw [dif_neg (fun h' => h (hiff.1 h')), dif_neg h]

lemma lid_bound (x : Fin m → ℝ) : ‖x‖ ≤ 1 * ‖(ContinuousLinearMap.id ℝ (Fin m → ℝ)) x‖ := by
  simp

lemma ofElem_cont' {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) :=
  continuous_sInf_rng.2 fun _ ht => ht.2 Γ k m n r s d π hs hπ

lemma J_cont' (N : ℕ) : Continuous (S.J N) :=
  ofElem_cont' (S.Gam N) (S.Kk N) (S.pres N) (S.stage_sp N) (S.pres_isElem N)

/-- transfer of a map of functions, stage by stage -/
lemma transfer {A2 : Type*} [AddCommGroup A2] [TopologicalSpace A2] [IsTopologicalAddGroup A2]
    {B2 : Type*} [AddCommGroup B2] [TopologicalSpace B2] [IsTopologicalAddGroup B2]
    (S2 : Setup A2 B2 m)
    (Tf : (Multiplicative A → ℂ) →ₗ[ℂ] (Multiplicative A2 → ℂ))
    (hT : ∀ N, ∃ (M : ℕ) (P : ((i : Fin (S2.sN M)) → ZMod (S2.dN M i)) → Prop)
      (c : ((i : Fin (S2.sN M)) → ZMod (S2.dN M i)) → ElemGroup m 0 0 (S.sN N) (S.dN N)),
      ∀ y : Aux_LF.ESp m (S.sN N) (S.dN N), S2.Good M (Tf (S.J N y).toFun) ∧
        ∀ q, Tf (S.J N y).toFun (S2.sec M q) =
          pbFun (ContinuousLinearMap.id ℝ (Fin m → ℝ)) P c y.toFun q) :
    ∃ T : SchwartzBruhat (Multiplicative A) →ₗ[ℂ] SchwartzBruhat (Multiplicative A2),
      (∀ f, (T f).toFun = Tf f.toFun) ∧ ∀ N, Continuous fun y => T (S.J N y) := by
  have key : ∀ N, ∃ (M : ℕ) (L : Aux_LF.ESp m (S.sN N) (S.dN N) →ₗ[ℂ]
      Aux_LF.ESp m (S2.sN M) (S2.dN M)), Continuous L ∧
      ∀ y, Tf (S.J N y).toFun = (S2.J M (L y)).toFun := by
    intro N
    obtain ⟨M, P, c, h⟩ := hT N
    refine ⟨M, pbLin (d := S2.dN M) (ContinuousLinearMap.id ℝ (Fin m → ℝ)) 1 zero_le_one
      lid_bound P c, pbLin_cont _ _ _ _ _ _, fun y => ?_⟩
    funext z
    rw [J_apply, pbLin_apply]
    have : pbFun (ContinuousLinearMap.id ℝ (Fin m → ℝ)) P c y.toFun =
        fun q => Tf (S.J N y).toFun (S2.sec M q) := funext fun q => ((h y).2 q).symm
    rw [this, S2.ext_good M _ (h y).1]
  have hmem : ∀ f : SchwartzBruhat (Multiplicative A),
      Tf f.toFun ∈ schwartzBruhatSubmodule (Multiplicative A2) := by
    intro f
    obtain ⟨N, hN⟩ := S.exists_good f
    obtain ⟨M, L, -, hL⟩ := key N
    rw [← S.JP_id N f hN, hL]
    exact (S2.J M (L (S.P N f))).2
  let T : SchwartzBruhat (Multiplicative A) →ₗ[ℂ] SchwartzBruhat (Multiplicative A2) :=
    { toFun := fun f => ⟨Tf f.toFun, hmem f⟩
      map_add' := fun f g => Subtype.ext (map_add Tf f.toFun g.toFun)
      map_smul' := fun c f => Subtype.ext (map_smul Tf c f.toFun) }
  refine ⟨T, fun f => rfl, fun N => ?_⟩
  obtain ⟨M, L, hLc, hL⟩ := key N
  have : (fun y => T (S.J N y)) = S2.J M ∘ L := by
    funext y; exact Subtype.ext (hL y)
  rw [this]
  exact (S2.J_cont' M).comp hLc

end Setup

end

end Aux_LFA


namespace Aux_LFA
open Aux_ESF

open MasulloGRH Topology Filter Set NumberField IsDedekindDomain

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

instance adeleTAG : IsTopologicalAddGroup (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (IsTopologicalAddGroup (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

/-- `ℝ^d × 𝔸_f ≅ 𝔸` -/
def eA : ((Fin (dimV F) → ℝ) × FiniteAdeleRing (𝓞 F) F) ≃+ AdeleRing (𝓞 F) F :=
  AddEquiv.prodCongr (eV F).symm (AddEquiv.refl (FiniteAdeleRing (𝓞 F) F))

/-- `ℝ^d × ∏_{S_f} F_v ≅ 𝔸_S` -/
def eS (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ((Fin (dimV F) → ℝ) × ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) ≃+
      SAdeleRing F Sf :=
  AddEquiv.prodCongr (eV F).symm (AddEquiv.refl _)

/-- the adelic setup -/
def SA : Setup (AdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F) (dimV F) :=
  ringSetup (finRD F) (eA F) ((cont_eV_symm F).prodMap continuous_id)
    ((cont_eV F).prodMap continuous_id)

/-- the `S`-adelic setup -/
def SS (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    Setup (SAdeleRing F Sf) ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) (dimV F) :=
  ringSetup (sRD F Sf) (eS F Sf) ((cont_eV_symm F).prodMap continuous_id)
    ((cont_eV F).prodMap continuous_id)

variable {F}

lemma SA_Y (z : Multiplicative (AdeleRing (𝓞 F) F)) : (SA F).Y z = (Multiplicative.toAdd z).2 := rfl
lemma SA_emb (x : Fin (dimV F) → ℝ) (a : FiniteAdeleRing (𝓞 F) F) :
    (SA F).emb x a = Multiplicative.ofAdd (((eV F).symm x, a) : AdeleRing (𝓞 F) F) := rfl
lemma SS_Y {Sf : Finset (HeightOneSpectrum (𝓞 F))} (z : Multiplicative (SAdeleRing F Sf)) :
    (SS F Sf).Y z = (Multiplicative.toAdd z).2 := rfl
lemma SS_emb {Sf : Finset (HeightOneSpectrum (𝓞 F))} (x : Fin (dimV F) → ℝ) (a) :
    (SS F Sf).emb x a = Multiplicative.ofAdd (((eV F).symm x, a) : SAdeleRing F Sf) := rfl

lemma fin_mul_apply (a b : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * b) v = a v * b v := rfl
lemma fin_sub_apply (a b : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (a - b) v = a v - b v := rfl

lemma memLA (N : ℕ) (a : FiniteAdeleRing (𝓞 F) F) : a ∈ (SA F).L N ↔
    ∀ v, ((N.factorial : ℕ) : v.adicCompletion F) * a v ∈ v.adicCompletionIntegers F := by
  show (∀ v, (((N.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) * a) v ∈ _) ↔ _
  simp only [fin_mul_apply, fin_nat_apply]

lemma memLS {Sf : Finset (HeightOneSpectrum (𝓞 F))} (N : ℕ) (a) : a ∈ (SS F Sf).L N ↔
    ∀ v : Sf, ((N.factorial : ℕ) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) * a v ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := by
  show (∀ v : Sf, (((N.factorial : ℕ) : (v' : Sf) → (v' : HeightOneSpectrum (𝓞 F)).adicCompletion F)
    * a) v ∈ _) ↔ _
  simp only [Pi.mul_apply, Pi.natCast_apply]

lemma memMA (N : ℕ) (a : FiniteAdeleRing (𝓞 F) F) : a ∈ (SA F).M N ↔
    ∃ y ∈ finO F, a = ((N.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) * y :=
  (finRD F).mem_M'

lemma memMS {Sf : Finset (HeightOneSpectrum (𝓞 F))} (N : ℕ) (a) : a ∈ (SS F Sf).M N ↔
    ∃ y ∈ sO F Sf, a = ((N.factorial : ℕ) : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) * y :=
  (sRD F Sf).mem_M'

/-! ### restriction and extension by zero -/

/-- restriction of a finite adele to `S_f` -/
def restr (Sf : Finset (HeightOneSpectrum (𝓞 F))) (a : FiniteAdeleRing (𝓞 F) F) :
    (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F := fun v => a v

open Classical in
/-- extension by zero -/
def extF (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (w : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  (⟨fun v => if h : v ∈ Sf then w ⟨v, h⟩ else 0, by
    have hs : {v : HeightOneSpectrum (𝓞 F) | ¬ ((if h : v ∈ Sf then w ⟨v, h⟩ else 0) ∈
        v.adicCompletionIntegers F)} ⊆ (Sf : Set (HeightOneSpectrum (𝓞 F))) := by
      intro v hv
      by_contra h
      apply hv
      rw [dif_neg (show v ∉ Sf from h)]
      exact zero_mem _
    exact Filter.eventually_cofinite.2 (Sf.finite_toSet.subset hs)⟩ :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)

open Classical in
lemma extF_apply (Sf : Finset (HeightOneSpectrum (𝓞 F))) (w) (v : HeightOneSpectrum (𝓞 F)) :
    extF Sf w v = if h : v ∈ Sf then w ⟨v, h⟩ else 0 := rfl

lemma extF_in (Sf : Finset (HeightOneSpectrum (𝓞 F))) (w) (v : Sf) : extF Sf w v = w v := by
  rw [extF_apply, dif_pos v.2]

lemma extF_out (Sf : Finset (HeightOneSpectrum (𝓞 F))) (w) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ Sf) : extF Sf w v = 0 := by
  rw [extF_apply, dif_neg hv]

lemma restr_extF (Sf : Finset (HeightOneSpectrum (𝓞 F))) (w) : restr Sf (extF Sf w) = w := by
  funext v; exact extF_in Sf w v

/-! ### the functions -/

open Classical in
/-- `π_S h (x) = h(x_S) · 1[x_v ∈ O_v for v ∉ S]` on functions -/
def piFun (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (Multiplicative (SAdeleRing F Sf) → ℂ) →ₗ[ℂ] (Multiplicative (AdeleRing (𝓞 F) F) → ℂ) where
  toFun h z := h (Multiplicative.ofAdd (((Multiplicative.toAdd z).1,
      restr Sf (Multiplicative.toAdd z).2) : SAdeleRing F Sf)) *
    (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → (Multiplicative.toAdd z).2 v ∈
      v.adicCompletionIntegers F then 1 else 0)
  map_add' f g := by funext z; simp only [Pi.add_apply, add_mul]
  map_smul' c f := by funext z; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

/-- `r_S h (y) = h(y, 0)` on functions -/
def rFun (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (Multiplicative (AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] (Multiplicative (SAdeleRing F Sf) → ℂ) where
  toFun h w := h (Multiplicative.ofAdd (((Multiplicative.toAdd w).1,
      extF Sf (Multiplicative.toAdd w).2) : AdeleRing (𝓞 F) F))
  map_add' f g := rfl
  map_smul' c f := rfl

lemma nat_mem_O (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ((n : ℕ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := natCast_mem _ n

/-! ### goodness transfers -/

lemma good_pi (Sf : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ)
    (h : Multiplicative (SAdeleRing F Sf) → ℂ) (hh : (SS F Sf).Good N h) :
    (SA F).Good N (piFun Sf h) := by
  classical
  refine ⟨fun z hz => ?_, fun x a a' ha => ?_⟩
  · show h _ * _ = 0
    by_cases hi : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → (Multiplicative.toAdd z).2 v ∈
        v.adicCompletionIntegers F
    · rw [if_pos hi]
      have : (SS F Sf).Y (Multiplicative.ofAdd (((Multiplicative.toAdd z).1,
          restr Sf (Multiplicative.toAdd z).2) : SAdeleRing F Sf)) ∉ (SS F Sf).L N := by
        rw [SS_Y, memLS]
        intro hS
        apply hz
        rw [SA_Y, memLA]
        intro v
        by_cases hv : v ∈ Sf
        · exact hS ⟨v, hv⟩
        · exact mul_mem (nat_mem_O v _) (hi v hv)
      rw [hh.1 _ this, zero_mul]
    · rw [if_neg hi, mul_zero]
  · obtain ⟨y, hy, hy'⟩ := (memMA N _).1 ha
    have hb : a' = a + ((N.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) * y := by rw [← hy']; abel
    have hc : ∀ v, a' v = a v + ((N.factorial : ℕ) : v.adicCompletion F) * y v := by
      intro v
      rw [hb, show (a + ((N.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) * y) v =
        a v + (((N.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) * y) v from rfl, fin_mul_apply,
        fin_nat_apply]
    rw [SA_emb, SA_emb]
    change h (Multiplicative.ofAdd (((eV F).symm x, restr Sf a) : SAdeleRing F Sf)) *
        (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → a v ∈ v.adicCompletionIntegers F then 1 else 0) =
      h (Multiplicative.ofAdd (((eV F).symm x, restr Sf a') : SAdeleRing F Sf)) *
        (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → a' v ∈ v.adicCompletionIntegers F then 1 else 0)
    have h1 : h (Multiplicative.ofAdd (((eV F).symm x, restr Sf a) : SAdeleRing F Sf)) =
        h (Multiplicative.ofAdd (((eV F).symm x, restr Sf a') : SAdeleRing F Sf)) := by
      rw [← SS_emb, ← SS_emb]
      refine hh.2 x _ _ ((memMS N _).2 ⟨restr Sf y, fun v => hy v, ?_⟩)
      funext v
      simp only [restr, Pi.sub_apply, Pi.mul_apply, Pi.natCast_apply]
      rw [hc]; ring
    have h2 : (∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → a v ∈ v.adicCompletionIntegers F) ↔
        (∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → a' v ∈ v.adicCompletionIntegers F) := by
      constructor
      · intro H v hv; rw [hc]; exact add_mem (H v hv) (mul_mem (nat_mem_O v _) (hy v))
      · intro H v hv
        have := sub_mem (H v hv) (mul_mem (nat_mem_O v N.factorial) (hy v))
        rwa [hc, add_sub_cancel_right] at this
    rw [h1, if_congr h2 rfl rfl]

lemma good_r (Sf : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ)
    (h : Multiplicative (AdeleRing (𝓞 F) F) → ℂ) (hh : (SA F).Good N h) :
    (SS F Sf).Good N (rFun Sf h) := by
  refine ⟨fun z hz => ?_, fun x a a' ha => ?_⟩
  · show h _ = 0
    refine hh.1 _ ?_
    rw [SA_Y, memLA]
    intro H
    apply hz
    rw [SS_Y, memLS]
    intro v
    have := H v
    change ((N.factorial : ℕ) : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) *
      extF Sf (Multiplicative.toAdd z).2 v ∈ _ at this
    rwa [extF_in] at this
  · obtain ⟨y, hy, hy'⟩ := (memMS N _).1 ha
    have hb : a' = a + ((N.factorial : ℕ) : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) * y := by
      rw [← hy']; abel
    rw [SS_emb, SS_emb]
    change h ((SA F).emb x (extF Sf a)) = h ((SA F).emb x (extF Sf a'))
    refine hh.2 x _ _ ((memMA N _).2 ⟨extF Sf y, fun v => ?_, ?_⟩)
    · by_cases hv : v ∈ Sf
      · rw [show v = ((⟨v, hv⟩ : Sf) : HeightOneSpectrum (𝓞 F)) from rfl, extF_in]
        exact hy ⟨v, hv⟩
      · rw [extF_out Sf y hv]; exact zero_mem _
    · refine FiniteAdeleRing.ext F fun v => ?_
      rw [fin_sub_apply, fin_mul_apply, fin_nat_apply]
      by_cases hv : v ∈ Sf
      · rw [show v = ((⟨v, hv⟩ : Sf) : HeightOneSpectrum (𝓞 F)) from rfl, extF_in, extF_in,
          extF_in, hb]
        simp only [Pi.add_apply, Pi.mul_apply, Pi.natCast_apply]
        abel
      · rw [extF_out _ _ hv, extF_out _ _ hv, extF_out _ _ hv, sub_zero, mul_zero]

/-! ### the stage formulas -/

open Classical in
lemma pi_stage (Sf : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ) :
    ∃ (P : ((i : Fin ((SA F).sN N)) → ZMod ((SA F).dN N i)) → Prop)
      (c : ((i : Fin ((SA F).sN N)) → ZMod ((SA F).dN N i)) →
        ElemGroup (dimV F) 0 0 ((SS F Sf).sN N) ((SS F Sf).dN N)),
      ∀ y : Aux_LF.ESp (dimV F) ((SS F Sf).sN N) ((SS F Sf).dN N),
        (SA F).Good N (piFun Sf ((SS F Sf).J N y).toFun) ∧
        ∀ q, piFun Sf ((SS F Sf).J N y).toFun ((SA F).sec N q) =
          pbFun (ContinuousLinearMap.id ℝ (Fin (dimV F) → ℝ)) P c y.toFun q := by
  refine ⟨fun b => restr Sf ((SA F).rep N b) ∈ (SS F Sf).L N ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → (SA F).rep N b v ∈ v.adicCompletionIntegers F,
    fun b => if h : restr Sf ((SA F).rep N b) ∈ (SS F Sf).L N then
      (0, 0, 0, (SS F Sf).del N ⟨_, h⟩) else 0, fun y => ⟨good_pi Sf N _ ((SS F Sf).good_J N y),
    fun q => ?_⟩⟩
  rw [Setup.sec_eq, SA_emb]
  change ((SS F Sf).J N y).toFun ((SS F Sf).emb q.1 (restr Sf ((SA F).rep N q.2.2.2))) *
    (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → (SA F).rep N q.2.2.2 v ∈
      v.adicCompletionIntegers F then 1 else 0) = _
  rw [Setup.J_apply, Setup.ep_emb]
  unfold pbFun
  by_cases h1 : restr Sf ((SA F).rep N q.2.2.2) ∈ (SS F Sf).L N
  · by_cases h2 : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → (SA F).rep N q.2.2.2 v ∈
        v.adicCompletionIntegers F
    · rw [dif_pos h1, if_pos h2, mul_one, if_pos ⟨h1, h2⟩]
      simp only [dif_pos h1]
      congr 1
      refine Prod.ext (by simp) (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp
    · rw [if_neg h2, mul_zero, if_neg (fun h => h2 h.2)]
  · rw [dif_neg h1, zero_mul, if_neg (fun h => h1 h.1)]

open Classical in
lemma r_stage (Sf : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ) :
    ∃ (P : ((i : Fin ((SS F Sf).sN N)) → ZMod ((SS F Sf).dN N i)) → Prop)
      (c : ((i : Fin ((SS F Sf).sN N)) → ZMod ((SS F Sf).dN N i)) →
        ElemGroup (dimV F) 0 0 ((SA F).sN N) ((SA F).dN N)),
      ∀ y : Aux_LF.ESp (dimV F) ((SA F).sN N) ((SA F).dN N),
        (SS F Sf).Good N (rFun Sf ((SA F).J N y).toFun) ∧
        ∀ q, rFun Sf ((SA F).J N y).toFun ((SS F Sf).sec N q) =
          pbFun (ContinuousLinearMap.id ℝ (Fin (dimV F) → ℝ)) P c y.toFun q := by
  refine ⟨fun b => extF Sf ((SS F Sf).rep N b) ∈ (SA F).L N,
    fun b => if h : extF Sf ((SS F Sf).rep N b) ∈ (SA F).L N then
      (0, 0, 0, (SA F).del N ⟨_, h⟩) else 0, fun y => ⟨good_r Sf N _ ((SA F).good_J N y),
    fun q => ?_⟩⟩
  rw [Setup.sec_eq, SS_emb]
  change ((SA F).J N y).toFun ((SA F).emb q.1 (extF Sf ((SS F Sf).rep N q.2.2.2))) = _
  rw [Setup.J_apply, Setup.ep_emb]
  unfold pbFun
  by_cases h1 : extF Sf ((SS F Sf).rep N q.2.2.2) ∈ (SA F).L N
  · rw [dif_pos h1, if_pos h1]
    simp only [dif_pos h1]
    congr 1
    refine Prod.ext (by simp) (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp
  · rw [dif_neg h1, if_neg h1]

/-! ### the maps -/

lemma maps_exist (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (π : SAdelicSchwartz F Sf →ₗ[ℂ] AdelicSchwartz F)
      (r : AdelicSchwartz F →ₗ[ℂ] SAdelicSchwartz F Sf),
      (∀ f, (π f).toFun = piFun Sf f.toFun) ∧ (∀ f, (r f).toFun = rFun Sf f.toFun) ∧
      (∀ N, Continuous fun y => π ((SS F Sf).J N y)) ∧
      (∀ N, Continuous fun y => r ((SA F).J N y)) := by
  obtain ⟨π, hπ1, hπ2⟩ := (SS F Sf).transfer (SA F) (piFun Sf) fun N => ⟨N, pi_stage Sf N⟩
  obtain ⟨r, hr1, hr2⟩ := (SA F).transfer (SS F Sf) (rFun Sf) fun N => ⟨N, r_stage Sf N⟩
  exact ⟨π, r, hπ1, hr1, hπ2, hr2⟩

lemma r_pi_fun (Sf : Finset (HeightOneSpectrum (𝓞 F))) (h : Multiplicative (SAdeleRing F Sf) → ℂ) :
    rFun Sf (piFun Sf h) = h := by
  classical
  funext w
  change h (Multiplicative.ofAdd (((Multiplicative.toAdd w).1, restr Sf (extF Sf
    (Multiplicative.toAdd w).2)) : SAdeleRing F Sf)) * (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
      extF Sf (Multiplicative.toAdd w).2 v ∈ v.adicCompletionIntegers F then 1 else 0) = h w
  rw [restr_extF, if_pos (fun v hv => by rw [extF_out _ _ hv]; exact zero_mem _), mul_one]
  rfl

/-! ### decomposition of adelic Schwartz–Bruhat functions -/

lemma kinv_mem (N : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ HeightOneSpectrum.Support (𝓞 F) (((N.factorial : ℕ) : F)⁻¹)) :
    ((((N.factorial : ℕ) : F)⁻¹ : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact not_lt.1 hv

lemma kinv_mul (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    ((((N.factorial : ℕ) : F)⁻¹ : F) : v.adicCompletion F) * ((N.factorial : ℕ) : v.adicCompletion F) = 1 := by
  rw [natc, ← HeightOneSpectrum.adicCompletion.coe_mul, inv_mul_cancel₀ (fact_ne F N),
    HeightOneSpectrum.adicCompletion.coe_one]

open Classical in
lemma decomp_fun (f : AdelicSchwartz F) : ∃ Tf : Finset (HeightOneSpectrum (𝓞 F)),
    ∀ x : AdeleRing (𝓞 F) F, f.toFun (Multiplicative.ofAdd x) =
      f.toFun (Multiplicative.ofAdd ((x.1, extF Tf (restr Tf x.2)) : AdeleRing (𝓞 F) F)) *
      (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Tf → x.2 v ∈ v.adicCompletionIntegers F then 1 else 0) := by
  obtain ⟨N, hN⟩ := (SA F).exists_good f
  let Tf := (HeightOneSpectrum.Support.finite (𝓞 F) (((N.factorial : ℕ) : F)⁻¹)).toFinset
  have hT : ∀ v, v ∉ Tf → v ∉ HeightOneSpectrum.Support (𝓞 F) (((N.factorial : ℕ) : F)⁻¹) :=
    fun v hv h => hv ((Set.Finite.mem_toFinset _).2 h)
  refine ⟨Tf, fun x => ?_⟩
  have hx : (Multiplicative.ofAdd x : Multiplicative (AdeleRing (𝓞 F) F)) =
      (SA F).emb (eV F x.1) x.2 := by
    rw [SA_emb, AddEquiv.symm_apply_apply]; rfl
  by_cases hi : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Tf → x.2 v ∈ v.adicCompletionIntegers F
  · rw [if_pos hi, mul_one]
    have hx' : (Multiplicative.ofAdd ((x.1, extF Tf (restr Tf x.2)) : AdeleRing (𝓞 F) F)) =
        (SA F).emb (eV F x.1) (extF Tf (restr Tf x.2)) := by
      rw [SA_emb, AddEquiv.symm_apply_apply]
    refine (congrArg f.toFun hx).trans ((hN.2 _ _ _ ?_).trans (congrArg f.toFun hx'.symm))
    -- the difference lies in `N! Ô`
    show (RingData.ci (finRD F) N) * (extF Tf (restr Tf x.2) - x.2) ∈ finO F
    have hci : RingData.ci (finRD F) N = algebraMap F (FiniteAdeleRing (𝓞 F) F) (((N.factorial : ℕ) : F)⁻¹) := by
      have h1 := (finRD F).ci_c N
      have h2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((N.factorial : ℕ) : F)⁻¹) *
          RingData.c (B := FiniteAdeleRing (𝓞 F) F) N = 1 := by
        rw [RingData.c, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul,
          inv_mul_cancel₀ (fact_ne F N), map_one]
      have hu := (finRD F).unit N
      calc RingData.ci (finRD F) N = RingData.ci (finRD F) N * (RingData.c N * RingData.ci (finRD F) N) := by
            rw [(finRD F).c_ci, mul_one]
        _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) (((N.factorial : ℕ) : F)⁻¹) *
              (RingData.c N * RingData.ci (finRD F) N) := by
            rw [← mul_assoc, ← mul_assoc, h1, h2]
        _ = _ := by rw [(finRD F).c_ci, mul_one]
    rw [hci]
    intro v
    show (algebraMap F (FiniteAdeleRing (𝓞 F) F) (((N.factorial : ℕ) : F)⁻¹)) v *
      (extF Tf (restr Tf x.2) - x.2) v ∈ _
    rw [FiniteAdeleRing.algebraMap_apply, fin_sub_apply]
    by_cases hv : v ∈ Tf
    · rw [show v = ((⟨v, hv⟩ : Tf) : HeightOneSpectrum (𝓞 F)) from rfl, extF_in]
      simp only [restr, sub_self, mul_zero]
      exact zero_mem _
    · rw [extF_out _ _ hv, zero_sub, mul_neg]
      exact neg_mem (mul_mem (kinv_mem N v (hT v hv)) (hi v hv))
  · rw [if_neg hi, mul_zero, hx]
    refine hN.1 _ ?_
    rw [Setup.Y_emb, memLA]
    intro H
    apply hi
    intro v hv
    have := mul_mem (kinv_mem N v (hT v hv)) (H v)
    rwa [← mul_assoc, kinv_mul, one_mul] at this

end

end Aux_LFA


namespace Aux_LF

open MasulloGRH NumberField IsDedekindDomain Aux_LFA

open Classical in
theorem sadeles_maps (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (π : SAdelicSchwartz F Sf →ₗ[ℂ] AdelicSchwartz F)
      (r : AdelicSchwartz F →ₗ[ℂ] SAdelicSchwartz F Sf),
      Continuous π ∧ Continuous r ∧ (∀ f, r (π f) = f) ∧
      ∀ (f : SAdelicSchwartz F Sf) (x : AdeleRing (𝓞 F) F),
        (π f).eval x = f.eval (x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F))) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → x.2 v ∈ v.adicCompletionIntegers F
            then 1 else 0) := by
  obtain ⟨π, r, hπ, hr, hπc, hrc⟩ := maps_exist Sf
  refine ⟨π, r, lin_cont (SS F Sf).toSBData sb_ws π hπc,
    lin_cont (SA F).toSBData sb_ws r hrc, fun f => ?_, fun f x => ?_⟩
  · apply Subtype.ext
    show (r (π f)).toFun = f.toFun
    rw [hr, hπ, r_pi_fun]
  · show (π f).toFun (Multiplicative.ofAdd x) = _
    rw [hπ]
    rfl

open Classical in
theorem adelic_decomp (F : Type*) [Field F] [NumberField F] (f : AdelicSchwartz F) :
    ∃ (Tf : Finset (HeightOneSpectrum (𝓞 F))) (f₀ : SAdelicSchwartz F Tf),
      ∀ x : AdeleRing (𝓞 F) F,
        f.eval x = f₀.eval (x.1, fun v : Tf => x.2 (v : HeightOneSpectrum (𝓞 F))) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Tf → x.2 v ∈ v.adicCompletionIntegers F
            then 1 else 0) := by
  obtain ⟨Tf, hT⟩ := decomp_fun f
  obtain ⟨π, r, -, hr, -, -⟩ := maps_exist Tf
  refine ⟨Tf, r f, fun x => ?_⟩
  show f.toFun (Multiplicative.ofAdd x) = (r f).toFun _ * _
  rw [hT x, hr]
  rfl

end Aux_LF


open MasulloGRH NumberField IsDedekindDomain Classical in
theorem solution (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (IsStrictLFOfNuclearFrechet (SAdelicSchwartz F Sf) ∧ IsHLCS (SAdelicSchwartz F Sf) ∧
      IsCompleteTVS (SAdelicSchwartz F Sf) ∧ IsNuclear (SAdelicSchwartz F Sf) ∧
      IsMontel (SAdelicSchwartz F Sf) ∧
      IsCompleteTVS (StrongDual ℂ (SAdelicSchwartz F Sf)) ∧
      IsNuclear (StrongDual ℂ (SAdelicSchwartz F Sf)) ∧
      IsMontel (StrongDual ℂ (SAdelicSchwartz F Sf))) ∧
    (∃ π : SAdelicSchwartz F Sf →ₗ[ℂ] AdelicSchwartz F, IsLinearTopologicalEmbedding π ∧
      ∀ (f : SAdelicSchwartz F Sf) (x : AdeleRing (𝓞 F) F),
        (π f).eval x =
          f.eval (x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F))) *
            (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → x.2 v ∈ v.adicCompletionIntegers F
              then 1 else 0)) ∧
    (∀ f : AdelicSchwartz F, ∃ (Tf : Finset (HeightOneSpectrum (𝓞 F)))
        (f₀ : SAdelicSchwartz F Tf), ∀ x : AdeleRing (𝓞 F) F,
      f.eval x =
        f₀.eval (x.1, fun v : Tf => x.2 (v : HeightOneSpectrum (𝓞 F))) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Tf → x.2 v ∈ v.adicCompletionIntegers F
            then 1 else 0)) := by
  obtain ⟨D⟩ := Aux_LF.sbdata_sadeles F Sf
  obtain ⟨a1, -, a3, a4, a5, a6, a7, a8, a9⟩ := Aux_LF.sb_all D
  obtain ⟨π, r, hπ, hr, hrπ, hev⟩ := Aux_LF.sadeles_maps F Sf
  refine ⟨⟨a1, a3, a4, a5, a6, a7, a8, a9⟩, ⟨π, ?_, hev⟩, Aux_LF.adelic_decomp F⟩
  exact Function.LeftInverse.isEmbedding (f := r) hrπ hr hπ
