-- Prove2me | solution 1 for MatrixTail.Azuma.lemma7_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:59:39.333595+00:00
-- url     : https://prove2.me/submissions/45d4c973-a796-4a2b-9315-071b605ee915

import Mathlib
import Definitions.Def_MatrixTail_Azuma_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal
open MatrixTail.Azuma

theorem mta_mexp_smul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (c : ℝ) :
    mexp (c • A) = cfc (fun x : ℝ => Real.exp (c * x)) A := by
  have hA' : IsSelfAdjoint A := hA
  unfold mexp
  rw [← cfc_comp_smul c Real.exp A]
  simp [smul_eq_mul]

theorem mta_cosh_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    (1 / 2 : ℝ) • (mexp (θ • A) + mexp ((-θ) • A)) ≤ mexp ((θ ^ 2 / 2) • A ^ 2) := by
  have hA' : IsSelfAdjoint A := hA
  rw [mta_mexp_smul A hA, mta_mexp_smul A hA]
  have c1 : Continuous (fun x : ℝ => Real.exp (θ * x)) := by fun_prop
  have c2 : Continuous (fun x : ℝ => Real.exp (-θ * x)) := by fun_prop
  have e1 : (1 / 2 : ℝ) • (cfc (fun x : ℝ => Real.exp (θ * x)) A + cfc (fun x : ℝ => Real.exp (-θ * x)) A) =
      cfc (fun x : ℝ => 1 / 2 * (Real.exp (θ * x) + Real.exp (-θ * x))) A := by
    rw [cfc_const_mul (1 / 2) (fun x : ℝ => Real.exp (θ * x) + Real.exp (-θ * x)) A
      (c1.add c2).continuousOn,
      cfc_add A (fun x : ℝ => Real.exp (θ * x)) (fun x : ℝ => Real.exp (-θ * x)) c1.continuousOn c2.continuousOn]
  have c3 : Continuous (fun x : ℝ => x ^ 2) := by fun_prop
  have c4 : Continuous (fun x : ℝ => θ ^ 2 / 2 * x ^ 2) := by fun_prop
  have e2 : mexp ((θ ^ 2 / 2) • A ^ 2) = cfc (fun x : ℝ => Real.exp (θ ^ 2 / 2 * x ^ 2)) A := by
    unfold mexp
    have h1 : (θ ^ 2 / 2) • A ^ 2 = cfc (fun x : ℝ => θ ^ 2 / 2 * x ^ 2) A := by
      rw [cfc_const_mul (θ ^ 2 / 2) (fun x : ℝ => x ^ 2) A c3.continuousOn, cfc_pow_id A 2]
    rw [h1, ← cfc_comp Real.exp (fun x : ℝ => θ ^ 2 / 2 * x ^ 2) A hA' Real.continuous_exp.continuousOn c4.continuousOn]
    rfl
  rw [e1, e2]
  refine cfc_mono (fun x _ => ?_) (c1.add c2 |>.const_mul (1/2) |>.continuousOn) (by fun_prop : Continuous (fun x : ℝ => Real.exp (θ ^ 2 / 2 * x ^ 2))).continuousOn
  have := Real.cosh_le_exp_half_sq (θ * x)
  rw [Real.cosh_eq] at this
  have h2 : (θ * x) ^ 2 / 2 = θ ^ 2 / 2 * x ^ 2 := by ring
  rw [h2] at this
  have h3 : -θ * x = -(θ * x) := by ring
  rw [h3]
  linarith

theorem mta_mean_rad {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (ε : Ω → ℝ) (hε : IsRademacher P ε) (θ : ℝ) :
    mean P (fun ω => mexp ((ε ω * θ) • A)) = (1 / 2 : ℝ) • (mexp (θ • A) + mexp ((-θ) • A)) := by
  obtain ⟨hεm, hp1, hp2⟩ := hε
  have hS1 : MeasurableSet {ω | ε ω = 1} := hεm (measurableSet_singleton 1)
  have hS2 : MeasurableSet {ω | ε ω = -1} := hεm (measurableSet_singleton (-1))
  have hdisj : Disjoint {ω | ε ω = 1} {ω | ε ω = -1} := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    rw [h1] at h2; norm_num at h2
  have hae : ∀ᵐ ω ∂P, ω ∈ {ω | ε ω = 1} ∪ {ω | ε ω = -1} := by
    have hU : P ({ω | ε ω = 1} ∪ {ω | ε ω = -1}) = 1 := by
      have h := measureReal_union hdisj hS2 (μ := P)
      rw [hp1, hp2] at h
      have h1 : P.real ({ω | ε ω = 1} ∪ {ω | ε ω = -1}) = 1 := by rw [h]; norm_num
      have := (ENNReal.toReal_eq_one_iff _).mp h1
      exact this
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (hS1.union hS2)).mpr hU
  ext i j
  have hrhs : ((1 / 2 : ℝ) • (mexp (θ • A) + mexp ((-θ) • A))) i j =
      (1 / 2 : ℝ) • (mexp (θ • A) i j + mexp ((-θ) • A) i j) := by simp
  rw [hrhs]
  unfold mean
  simp only [Matrix.of_apply]
  have hF : (fun ω => mexp ((ε ω * θ) • A) i j) =ᵐ[P]
      fun ω => {ω | ε ω = 1}.indicator (fun _ => mexp (θ • A) i j) ω +
        {ω | ε ω = -1}.indicator (fun _ => mexp ((-θ) • A) i j) ω := by
    filter_upwards [hae] with ω hω
    rcases hω with h | h
    · have h' : ε ω = 1 := h
      have h2 : ω ∉ {ω | ε ω = -1} := by
        intro h3; simp only [Set.mem_setOf_eq] at h3; rw [h'] at h3; norm_num at h3
      rw [Set.indicator_of_mem h, Set.indicator_of_notMem h2, h']
      simp
    · have h' : ε ω = -1 := h
      have h2 : ω ∉ {ω | ε ω = 1} := by
        intro h3; simp only [Set.mem_setOf_eq] at h3; rw [h'] at h3; norm_num at h3
      rw [Set.indicator_of_mem h, Set.indicator_of_notMem h2, h']
      simp
  rw [integral_congr_ae hF, integral_add ((integrable_const _).indicator hS1) ((integrable_const _).indicator hS2),
    integral_indicator_const _ hS1, integral_indicator_const _ hS2, hp1, hp2]
  simp


theorem mta_log_cosh_le {d : ℕ} (x : Matrix (Fin d) (Fin d) ℂ) (hx : x.IsHermitian) (θ : ℝ) :
    mlog ((1 / 2 : ℝ) • (mexp (θ • x) + mexp ((-θ) • x))) ≤ (θ ^ 2 / 2) • x ^ 2 := by
  have hx' : IsSelfAdjoint x := hx
  rw [mta_mexp_smul x hx, mta_mexp_smul x hx]
  have c1 : Continuous (fun a : ℝ => Real.exp (θ * a)) := by fun_prop
  have c2 : Continuous (fun a : ℝ => Real.exp (-θ * a)) := by fun_prop
  have e1 : (1 / 2 : ℝ) • (cfc (fun a : ℝ => Real.exp (θ * a)) x + cfc (fun a : ℝ => Real.exp (-θ * a)) x) =
      cfc (fun a : ℝ => 1 / 2 * (Real.exp (θ * a) + Real.exp (-θ * a))) x := by
    rw [cfc_const_mul (1 / 2) (fun a : ℝ => Real.exp (θ * a) + Real.exp (-θ * a)) x
      (c1.add c2).continuousOn,
      cfc_add x (fun a : ℝ => Real.exp (θ * a)) (fun a : ℝ => Real.exp (-θ * a)) c1.continuousOn c2.continuousOn]
  have hpos : ∀ a : ℝ, 0 < 1 / 2 * (Real.exp (θ * a) + Real.exp (-θ * a)) := fun a => by positivity
  have c5 : Continuous (fun a : ℝ => 1 / 2 * (Real.exp (θ * a) + Real.exp (-θ * a))) := by fun_prop
  have clog : ContinuousOn Real.log ((fun a : ℝ => 1 / 2 * (Real.exp (θ * a) + Real.exp (-θ * a))) '' spectrum ℝ x) := by
    refine Real.continuousOn_log.mono ?_
    rintro _ ⟨a, _, rfl⟩
    exact (hpos a).ne'
  have e2 : mlog (cfc (fun a : ℝ => 1 / 2 * (Real.exp (θ * a) + Real.exp (-θ * a))) x) =
      cfc (fun a : ℝ => Real.log (1 / 2 * (Real.exp (θ * a) + Real.exp (-θ * a)))) x := by
    unfold mlog
    exact (cfc_comp Real.log (fun a : ℝ => 1 / 2 * (Real.exp (θ * a) + Real.exp (-θ * a))) x hx' clog c5.continuousOn).symm
  have c3 : Continuous (fun a : ℝ => a ^ 2) := by fun_prop
  have e3 : (θ ^ 2 / 2) • x ^ 2 = cfc (fun a : ℝ => θ ^ 2 / 2 * a ^ 2) x := by
    rw [cfc_const_mul (θ ^ 2 / 2) (fun a : ℝ => a ^ 2) x c3.continuousOn, cfc_pow_id x 2]
  rw [e1, e2, e3]
  have hcont : ContinuousOn (fun a : ℝ => Real.log (1 / 2 * (Real.exp (θ * a) + Real.exp (-θ * a)))) (spectrum ℝ x) :=
    clog.comp c5.continuousOn (Set.mapsTo_image _ _)
  refine cfc_mono (fun a _ => ?_) hcont (by fun_prop : Continuous (fun a : ℝ => θ ^ 2 / 2 * a ^ 2)).continuousOn
  have := Real.cosh_le_exp_half_sq (θ * a)
  rw [Real.cosh_eq] at this
  have h3 : -θ * a = -(θ * a) := by ring
  rw [h3]
  calc Real.log (1 / 2 * (Real.exp (θ * a) + Real.exp (-(θ * a))))
      ≤ Real.log (Real.exp ((θ * a) ^ 2 / 2)) := by
        apply Real.log_le_log
        · have := hpos a; rw [h3] at this; exact this
        · linarith [this]
    _ = θ ^ 2 / 2 * a ^ 2 := by rw [Real.log_exp]; ring

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (x A : Matrix (Fin d) (Fin d) ℂ) (hx : x.IsHermitian) (hA : A.IsHermitian)
    (hxA : x ^ 2 ≤ A ^ 2) (ε : Ω → ℝ) (hε : IsRademacher P ε) (θ : ℝ) :
    mlog (mean P (fun ω => mexp ((2 * ε ω * θ) • x))) ≤ (2 * θ ^ 2) • A ^ 2 := by
  have h1 : (fun ω => mexp ((2 * ε ω * θ) • x)) = fun ω => mexp ((ε ω * (2 * θ)) • x) := by
    funext ω; congr 2; ring
  rw [h1, mta_mean_rad P x ε hε (2 * θ)]
  refine le_trans (mta_log_cosh_le x hx (2 * θ)) ?_
  have e : (2 * θ) ^ 2 / 2 = 2 * θ ^ 2 := by ring
  rw [e]
  have h0 : (0 : ℝ) ≤ 2 * θ ^ 2 := by positivity
  exact smul_le_smul_of_nonneg_left hxA h0
