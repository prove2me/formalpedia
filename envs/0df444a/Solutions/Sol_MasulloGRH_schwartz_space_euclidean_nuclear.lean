-- Prove2me | solution 1 for MasulloGRH.schwartz_space_euclidean_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T07:12:13.217189+00:00
-- url     : https://prove2.me/submissions/b313447b-abea-4352-9b23-a30584e15a7b

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

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

lemma c1 : IsNuclear (Sch m) := by
  refine nuclear_of_frame (sch_hlcs_ws m) (fun j => phiF j.1 j.2) (fun j => eF j.1 j.2) cw ?_ ?_ ?_ ?_
  · exact frame_hasSum
  · exact cw_pos
  · exact cw_summable
  · exact frame_dom

lemma c2a : IsLocallyConvexTopology (Sch m) inferInstance := lc_of_ws (sch_hlcs_ws m)

lemma c2b : IsCompleteTVS (Sch m) := ctvs_of_complete

lemma c2c : TopologicalSpace.MetrizableSpace (Sch m) := UniformSpace.metrizableSpace

lemma c2 : IsFrechet (Sch m) := ⟨c2a m, c2b m, c2c m⟩

lemma c3a (Ψ : StrongDual ℂ (StrongDual ℂ (Sch m))) : ∃! x : Sch m, ∀ T : StrongDual ℂ (Sch m), Ψ T = T x := by
  refine srefl (sch_hlcs_ws m) (fun j => phiF j.1 j.2) (fun j => eF j.1 j.2) cw ?_ ?_ ?_ ?_ Ψ
  · exact frame_hasSum
  · exact cw_pos
  · exact cw_summable
  · exact frame_dom

lemma c3b : (inferInstance : TopologicalSpace (Sch m)) = strongBidualTopology (Sch m) :=
  sbE (sch_hlcs_ws m)

lemma c3 : IsReflexive (Sch m) := ⟨c3a m, c3b m⟩

lemma c4 : IsCompleteTVS (StrongDual ℂ (Sch m)) := ctvs_of_complete

lemma c5 : IsNuclear (StrongDual ℂ (Sch m)) := by
  refine dual_nuclear_of_frame (sch_hlcs_ws m) (fun j => phiF j.1 j.2) (fun j => eF j.1 j.2) cw
    ?_ ?_ ?_ ?_
  · exact frame_hasSum
  · exact cw_pos
  · exact cw_summable
  · exact frame_dom

lemma c6a : IsHLCS (StrongDual ℂ (Sch m)) := ⟨lc_of_ws (dws (E := Sch m)), inferInstance⟩

lemma c6b (A : Set (StrongDual ℂ (Sch m))) (hAc : IsClosed A) (hAb : IsVonNBounded ℂ A) :
    IsCompact A := by
  refine dual_compact (sch_hlcs_ws m) (fun j => phiF j.1 j.2) (fun j => eF j.1 j.2) cw
    ?_ ?_ ?_ ?_ A hAc hAb
  · exact frame_hasSum
  · exact cw_pos
  · exact cw_summable
  · exact frame_dom

lemma c6c : IsReflexive (StrongDual ℂ (Sch m)) := drefl (sch_hlcs_ws m) (c3a m)

lemma c6 : IsMontel (StrongDual ℂ (Sch m)) := ⟨c6a m, c6b m, c6c m⟩

theorem sch_all :
    IsNuclear (Sch m) ∧ IsFrechet (Sch m) ∧ IsReflexive (Sch m) ∧
    IsCompleteTVS (StrongDual ℂ (Sch m)) ∧ IsNuclear (StrongDual ℂ (Sch m)) ∧
    IsMontel (StrongDual ℂ (Sch m)) :=
  ⟨c1 m, c2 m, c3 m, c4 m, c5 m, c6 m⟩

end asm

end

end Aux_SEN


open MasulloGRH in
theorem solution (m : ℕ) :
    IsNuclear (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) ∧
    IsFrechet (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) ∧
    IsReflexive (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) ∧
    IsCompleteTVS (StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)) ∧
    IsNuclear (StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)) ∧
    IsMontel (StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)) :=
  Aux_SEN.sch_all m
