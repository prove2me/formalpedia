-- Prove2me | solution 1 for MaxPointDerivatives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:50:33.083072+00:00
-- url     : https://prove2.me/submissions/92616257-2c32-4a3e-b70f-7619734eb235

module
public import Definitions.Def_PHarmonicPoly_GradientEuler
public import Definitions.Def_PHarmonicPoly_MvPolyFDeriv
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Definitions.Def_PHarmonicPoly_MaxPointDerivatives
public import Theorems.Thm_GradientEuler
public import Theorems.Thm_MvPolyFDeriv
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradientInner


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n m : ℕ} (hm : 1 ≤ m) {P : MvPolynomial (Fin n) ℝ}
    (hhom : P.IsHomogeneous m)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    (hmax : MvPolynomial.eval (fun i => e i) P = 1)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
      |MvPolynomial.eval (fun i => y i) P| ≤ 1) :
    gradient (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
        = (m : ℝ) • e
      ∧ iteratedFDeriv ℝ 2
          (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e ![e, e]
        = (m : ℝ) * ((m : ℝ) - 1) := by
  have hee : (inner ℝ e e : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
  have hstep1 : (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => q i) P) e) e : ℝ) = (m : ℝ) := by
    have h := (GradientEuler hm hhom e e).1
    rw [hmax, mul_one] at h
    exact h
  have hstep2 : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → (inner ℝ e v : ℝ) = 0 →
      (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => q i) P) e) v : ℝ) = 0 := by
    intro v hv hev
    have hvv : (inner ℝ v v : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, hv]
      norm_num
    have hve : (inner ℝ v e : ℝ) = 0 := by
      rw [real_inner_comm]
      exact hev
    have hnorm : ∀ t : ℝ,
        ‖(Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      intro t
      have hsq : ‖(Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, hvv, hee, hev, hve]
        nlinarith [Real.sin_sq_add_cos_sq t]
      nlinarith [norm_nonneg (Real.cos t • e + Real.sin t • v :
        EuclideanSpace ℝ (Fin n)), hsq]
    have hcurve : HasDerivAt (fun t : ℝ =>
        (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)))
        ((-Real.sin (0:ℝ)) • e + Real.cos (0:ℝ) • v) 0 :=
      ((Real.hasDerivAt_cos 0).smul_const e).add ((Real.hasDerivAt_sin 0).smul_const v)
    have hc0 : ((-Real.sin (0:ℝ)) • e + Real.cos (0:ℝ) • v
        : EuclideanSpace ℝ (Fin n)) = v := by simp
    have hfd : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => z i) P)
        (∑ i, (MvPolynomial.eval (fun j => e j) (pderiv i P)) •
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        ((fun t : ℝ => (Real.cos t • e + Real.sin t • v
          : EuclideanSpace ℝ (Fin n))) 0) := by
      simpa using MvPolyFDerivEuclidean P e
    have hg : HasDerivAt (fun t : ℝ => MvPolynomial.eval
          (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P)
        ((∑ i, (MvPolynomial.eval (fun j => e j) (pderiv i P)) •
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) v) 0 := by
      have h := HasFDerivAt.comp_hasDerivAt (0:ℝ) hfd hcurve
      rw [hc0] at h
      exact h
    have hmaxloc : IsLocalMax (fun t : ℝ => MvPolynomial.eval
        (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P) 0 := by
      refine Filter.Eventually.of_forall (fun t => ?_)
      simp only
      rw [show (Real.cos (0:ℝ) • e + Real.sin (0:ℝ) • v
        : EuclideanSpace ℝ (Fin n)) = e from by simp, hmax]
      exact (abs_le.mp (hbd _ (hnorm t))).2
    have hzero := hmaxloc.hasDerivAt_eq_zero hg
    rw [(MvPolyGradientInner P e v).2] at hzero
    exact hzero
  have hGperp : ∀ w : EuclideanSpace ℝ (Fin n),
      (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => q i) P) e - (m:ℝ) • e) w : ℝ) = 0 := by
    intro w
    have hGe : (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => q i) P) e - (m:ℝ) • e) e : ℝ) = 0 := by
      rw [inner_sub_left, real_inner_smul_left, hstep1, hee]
      ring
    have hperp : (inner ℝ e (w - (inner ℝ w e : ℝ) • e) : ℝ) = 0 := by
      rw [inner_sub_right, real_inner_smul_right, hee, real_inner_comm e w]
      ring
    have hrest : (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => q i) P) e - (m:ℝ) • e)
        (w - (inner ℝ w e : ℝ) • e) : ℝ) = 0 := by
      rcases eq_or_ne (w - (inner ℝ w e : ℝ) • e) 0 with h | h
      · rw [h, inner_zero_right]
      · have hn0 : ‖w - (inner ℝ w e : ℝ) • e‖ ≠ 0 := norm_ne_zero_iff.mpr h
        have hvnorm : ‖(‖w - (inner ℝ w e : ℝ) • e‖⁻¹ •
            (w - (inner ℝ w e : ℝ) • e) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
          rw [norm_smul]
          simp [hn0]
        have hvperp : (inner ℝ e (‖w - (inner ℝ w e : ℝ) • e‖⁻¹ •
            (w - (inner ℝ w e : ℝ) • e) : EuclideanSpace ℝ (Fin n)) : ℝ) = 0 := by
          rw [real_inner_smul_right, hperp, mul_zero]
        have hev := hstep2 _ hvnorm hvperp
        have hsmall : (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => q i) P) e - (m:ℝ) • e)
            (‖w - (inner ℝ w e : ℝ) • e‖⁻¹ •
              (w - (inner ℝ w e : ℝ) • e) : EuclideanSpace ℝ (Fin n)) : ℝ) = 0 := by
          rw [inner_sub_left, real_inner_smul_left, hev]
          rw [hvperp]
          ring
        have hback : (w - (inner ℝ w e : ℝ) • e) =
            ‖w - (inner ℝ w e : ℝ) • e‖ • (‖w - (inner ℝ w e : ℝ) • e‖⁻¹ •
              (w - (inner ℝ w e : ℝ) • e)) := by
          rw [smul_smul, mul_inv_cancel₀ hn0, one_smul]
        rw [hback, real_inner_smul_right, hsmall, mul_zero]
    have hdecomp : (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => q i) P) e - (m:ℝ) • e) w : ℝ)
        = (inner ℝ w e : ℝ) * (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => q i) P) e - (m:ℝ) • e) e : ℝ)
          + (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => q i) P) e - (m:ℝ) • e)
            (w - (inner ℝ w e : ℝ) • e) : ℝ) := by
      rw [inner_sub_right, real_inner_smul_right]
      ring
    rw [hdecomp, hGe, hrest]
    ring
  have hstep3 : gradient (fun x : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => x i) P) e = (m : ℝ) • e := by
    have h0 := hGperp (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => q i) P) e - (m:ℝ) • e)
    have hz := inner_self_eq_zero.mp h0
    rw [sub_eq_zero] at hz
    exact hz
  refine ⟨hstep3, ?_⟩
  have h := (GradientEuler hm hhom e e).2
  rw [hstep1] at h
  rw [h]
  ring
