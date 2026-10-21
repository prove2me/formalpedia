-- Prove2me | solution 1 for NewtonCartan.geometrization_curvConds
-- status  : ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:50:31.804704+00:00
-- url     : https://prove2.me/submissions/5bdee9d0-89d7-4d86-bd44-3e1e6bbd843f

import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_riem_geomGamma
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped ContDiff BigOperators
open Classical
open NewtonCartan

/-! Malament Prop. 4.2.1 (G3): CurvConds after Trautman geometrization. -/

/-- Covariant derivative of the raised gradient: `∇_d ∇^a φ`. -/
noncomputable def covGrad (Γ : Conn) (φ : E → ℝ) (x : E) (d a : Fin 4) : ℝ :=
  pd (fun y => gradUp φ y a) d x + ∑ e : Fin 4, Γ x a d e * gradUp φ x e

private lemma riem_as_covGrad (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (x : E) (a b c d : Fin 4) :
    riem (geomΓ Γ φ) x a b c d =
      tt b * (tt c * covGrad Γ φ x d a - tt d * covGrad Γ φ x c a) := by
  simpa [covGrad] using riem_geomGamma Γ φ hNG x a b c d

private lemma tt_hh_vanish (n b : Fin 4) : tt n * hh n b = 0 := by
  simp only [tt, hh]; split_ifs <;> simp_all

private lemma hh_symm (a b : Fin 4) : hh a b = hh b a := by
  simp only [hh]; by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

private lemma contDiff_pd (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (b : Fin 4) :
    ContDiff ℝ ∞ (fun x => pd φ b x) := by
  have hf := (contDiff_infty_iff_fderiv.1 hφ).2
  simpa [pd] using ContDiff.clm_apply hf contDiff_const

private lemma pd2_symm (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : E) (a b : Fin 4) :
    pd2 φ a b x = pd2 φ b a x := by
  have hf : ContDiffAt ℝ ∞ φ x := hφ.contDiffAt
  have hsymm : IsSymmSndFDerivAt ℝ φ x :=
    hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]; decide)
  have key (i j : Fin 4) :
      pd2 φ i j x = fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single j 1) := by
    simp only [pd2, pd]
    have hu : DifferentiableAt ℝ (fderiv ℝ φ) x :=
      (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have h := fderiv_clm_apply (c := fderiv ℝ φ) (u := fun _ : E => Pi.single j (1 : ℝ))
      hu (differentiableAt_const _)
    have h' := congrArg (fun L : E →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) h
    simpa [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, fderiv_const, zero_apply] using h'
  rw [key a b, key b a]
  exact hsymm (Pi.single a 1) (Pi.single b 1)

private lemma hess_symm (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (x : E) (a b : Fin 4) : hess Γ φ x a b = hess Γ φ x b a := by
  simp only [hess, pd2_symm φ hNG.2.2 x a b, hNG.1.1.2 x _ a b]

private lemma compat_sum (Γ : Conn) (hC : Compatible Γ) (x : E) (a d m : Fin 4) :
    (∑ n : Fin 4, (Γ x a d n * hh n m + Γ x m d n * hh a n)) = 0 :=
  hC.2 x d a m

private lemma pd_gradUp (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : E) (d a : Fin 4) :
    pd (fun y => gradUp φ y a) d x = ∑ n : Fin 4, hh a n * pd2 φ d n x := by
  change (fderiv ℝ (fun y => ∑ n : Fin 4, hh a n * pd φ n y) x) (Pi.single d 1) =
    ∑ n : Fin 4, hh a n * pd2 φ d n x
  have hdiff (n : Fin 4) : DifferentiableAt ℝ (fun y => hh a n * pd φ n y) x :=
    (ContDiff.differentiable (contDiff_const.mul (contDiff_pd φ hφ n)) (by simp)).differentiableAt
  rw [fderiv_fun_sum (fun n _ => hdiff n)]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hf : DifferentiableAt ℝ (fun y => pd φ n y) x :=
    (ContDiff.differentiable (contDiff_pd φ hφ n) (by simp)).differentiableAt
  have hmul := fderiv_const_mul hf (hh a n)
  have h' := congrArg (fun L : E →L[ℝ] ℝ => L (Pi.single d (1 : ℝ))) hmul
  simpa [pd2, pd, smul_apply] using h'

private lemma christoffel_raise (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (x : E) (d a : Fin 4) :
    (∑ e : Fin 4, Γ x a d e * gradUp φ x e) =
      -∑ n : Fin 4, hh a n * (∑ e : Fin 4, Γ x e d n * pd φ e x) := by
  have hC : Compatible Γ := hNG.1.2
  have h1 :
      (∑ e : Fin 4, Γ x a d e * gradUp φ x e) =
        ∑ m : Fin 4, (∑ e : Fin 4, Γ x a d e * hh e m) * pd φ m x := by
    simp only [gradUp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
  have hcompat (m : Fin 4) :
      (∑ e : Fin 4, Γ x a d e * hh e m) = -∑ e : Fin 4, Γ x m d e * hh a e := by
    have hs := compat_sum Γ hC x a d m
    have hsplit :
        (∑ e : Fin 4, Γ x a d e * hh e m) + (∑ e : Fin 4, Γ x m d e * hh a e) =
          ∑ e : Fin 4, (Γ x a d e * hh e m + Γ x m d e * hh a e) :=
      (Finset.sum_add_distrib).symm
    linarith
  have h2 :
      (∑ m : Fin 4, (∑ e : Fin 4, Γ x a d e * hh e m) * pd φ m x) =
        -∑ m : Fin 4, (∑ e : Fin 4, Γ x m d e * hh a e) * pd φ m x := by
    simp only [hcompat, neg_mul, Finset.sum_neg_distrib]
  have h3 :
      (∑ m : Fin 4, (∑ e : Fin 4, Γ x m d e * hh a e) * pd φ m x) =
        ∑ n : Fin 4, hh a n * (∑ e : Fin 4, Γ x e d n * pd φ e x) := by
    have step1 :
        (∑ m : Fin 4, (∑ e : Fin 4, Γ x m d e * hh a e) * pd φ m x) =
          ∑ m : Fin 4, ∑ e : Fin 4, (Γ x m d e * hh a e * pd φ m x) :=
      Finset.sum_congr rfl fun m _ => by rw [Finset.sum_mul]
    have step2 :
        (∑ m : Fin 4, ∑ e : Fin 4, (Γ x m d e * hh a e * pd φ m x)) =
          ∑ e : Fin 4, ∑ m : Fin 4, (hh a e * Γ x m d e * pd φ m x) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun m _ => by ring
    have step3 :
        (∑ e : Fin 4, ∑ m : Fin 4, (hh a e * Γ x m d e * pd φ m x)) =
          ∑ n : Fin 4, hh a n * (∑ e : Fin 4, Γ x e d n * pd φ e x) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    exact step1.trans (step2.trans step3)
  rw [h1, h2, h3]

private lemma covGrad_eq_hess (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (x : E) (d a : Fin 4) :
    covGrad Γ φ x d a = ∑ n : Fin 4, hh a n * hess Γ φ x d n := by
  simp only [covGrad, hess, pd_gradUp φ hNG.2.2 x d a, christoffel_raise Γ φ hNG x d a]
  simp [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  abel

private lemma covGrad_time (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (x : E) (b : Fin 4) : covGrad Γ φ x b 0 = 0 := by
  rw [covGrad_eq_hess Γ φ hNG x b 0]
  exact Finset.sum_eq_zero fun n _ => by simp [hh]

private lemma sum_covGrad_eq_lap (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ) (x : E) :
    (∑ n : Fin 4, covGrad Γ φ x n n) = lap Γ φ x := by
  simp only [lap, covGrad_eq_hess Γ φ hNG]

/-- `R^a{}_b{}^c{}_d = -t_b t_d ∇^c ∇^a φ`. -/
private lemma riemUp3_formula (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ)
    (x : E) (a b c d : Fin 4) :
    riemUp3 (geomΓ Γ φ) x a b c d =
      -(tt b * tt d * ∑ n : Fin 4, covGrad Γ φ x n a * hh n c) := by
  simp only [riemUp3]
  have hterm (n : Fin 4) :
      riem (geomΓ Γ φ) x a b n d * hh n c =
        tt b * (tt n * covGrad Γ φ x d a - tt d * covGrad Γ φ x n a) * hh n c := by
    rw [riem_as_covGrad Γ φ hNG]
  simp only [hterm]
  -- Pointwise expand then sum
  have hpt (n : Fin 4) :
      tt b * (tt n * covGrad Γ φ x d a - tt d * covGrad Γ φ x n a) * hh n c =
        tt b * tt n * hh n c * covGrad Γ φ x d a -
          tt b * tt d * covGrad Γ φ x n a * hh n c := by ring
  simp only [hpt, Finset.sum_sub_distrib]
  have hvan :
      (∑ n : Fin 4, tt b * tt n * hh n c * covGrad Γ φ x d a) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    have h0 := tt_hh_vanish n c
    calc
      tt b * tt n * hh n c * covGrad Γ φ x d a
          = tt b * (tt n * hh n c) * covGrad Γ φ x d a := by ring
      _ = tt b * 0 * covGrad Γ φ x d a := by rw [h0]
      _ = 0 := by ring
  have hfac :
      (∑ n : Fin 4, tt b * tt d * covGrad Γ φ x n a * hh n c) =
        tt b * tt d * ∑ n : Fin 4, covGrad Γ φ x n a * hh n c := by
    simp [Finset.mul_sum, mul_assoc]
  rw [hvan, hfac, zero_sub]

theorem solution (Γ : Conn) (φ ρ : E → ℝ) (hNG : IsNG Γ φ)
    (_hρ : ContDiff ℝ ∞ ρ) (hP : Poisson Γ φ ρ) :
    CurvConds (geomΓ Γ φ) ρ := by
  refine ⟨?ric, ?sym, ?up2⟩
  · intro x a b
    simp only [ricci]
    have hsum :
        (∑ n : Fin 4, riem (geomΓ Γ φ) x n a b n) =
          tt a * tt b * (∑ n : Fin 4, covGrad Γ φ x n n) := by
      have hterm (n : Fin 4) :
          riem (geomΓ Γ φ) x n a b n =
            tt a * (tt b * covGrad Γ φ x n n - tt n * covGrad Γ φ x b n) := by
        rw [riem_as_covGrad Γ φ hNG]
      simp only [hterm]
      have hpt (n : Fin 4) :
          tt a * (tt b * covGrad Γ φ x n n - tt n * covGrad Γ φ x b n) =
            tt a * tt b * covGrad Γ φ x n n - tt a * tt n * covGrad Γ φ x b n := by ring
      simp only [hpt, Finset.sum_sub_distrib]
      have hfac1 :
          (∑ n : Fin 4, tt a * tt b * covGrad Γ φ x n n) =
            tt a * tt b * ∑ n : Fin 4, covGrad Γ φ x n n := by
        simp [Finset.mul_sum, mul_assoc]
      have hvan : (∑ n : Fin 4, tt a * tt n * covGrad Γ φ x b n) = 0 := by
        have : (∑ n : Fin 4, tt n * covGrad Γ φ x b n) = covGrad Γ φ x b 0 := by
          simp [tt, Finset.sum_ite_eq']
        simp only [mul_assoc, ← Finset.mul_sum]
        rw [show (∑ n : Fin 4, tt n * covGrad Γ φ x b n) = covGrad Γ φ x b 0 by
          simp [tt, Finset.sum_ite_eq']]
        rw [covGrad_time Γ φ hNG x b, mul_zero]
      rw [hfac1, hvan, sub_zero]
    rw [hsum, sum_covGrad_eq_lap Γ φ hNG x, hP x]
    ring
  · intro x a b c d
    rw [riemUp3_formula Γ φ hNG, riemUp3_formula Γ φ hNG]
    have hmul : tt b * tt d = tt d * tt b := by ring
    have hL :
        (∑ n : Fin 4, covGrad Γ φ x n a * hh n c) =
          ∑ n : Fin 4, ∑ m : Fin 4, hh c n * hh a m * hess Γ φ x n m := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [covGrad_eq_hess Γ φ hNG, hh_symm n c, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hR :
        (∑ n : Fin 4, covGrad Γ φ x n c * hh n a) =
          ∑ n : Fin 4, ∑ m : Fin 4, hh a n * hh c m * hess Γ φ x n m := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [covGrad_eq_hess Γ φ hNG, hh_symm n a, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hEq :
        (∑ n : Fin 4, ∑ m : Fin 4, hh c n * hh a m * hess Γ φ x n m) =
          ∑ n : Fin 4, ∑ m : Fin 4, hh a n * hh c m * hess Γ φ x n m := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
      rw [hess_symm Γ φ hNG x m n]
      ring
    rw [hL, hR, hEq, hmul]
  · intro x a b c d
    simp only [riemUp2]
    apply Finset.sum_eq_zero
    intro n _
    rw [riem_as_covGrad Γ φ hNG x a n c d]
    have := tt_hh_vanish n b
    calc
      (tt n * (tt c * covGrad Γ φ x d a - tt d * covGrad Γ φ x c a)) * hh n b
          = (tt n * hh n b) *
            (tt c * covGrad Γ φ x d a - tt d * covGrad Γ φ x c a) := by ring
      _ = 0 := by simp [this]
