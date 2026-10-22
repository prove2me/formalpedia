-- Prove2me | solution 1 for NewtonCartan.riem00_spatial_closed_F
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:42:57.959478+00:00
-- url     : https://prove2.me/submissions/6ab166d2-a2ae-493c-bc17-3056f9755ec7

import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_classical_christoffel_form
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped ContDiff BigOperators
open Classical
open NewtonCartan

private lemma tt_zero : tt (0 : Fin 4) = 1 := rfl

private lemma gamma0 (Γ : Conn) (hΓ : IsClassical Γ) :
    ∀ x b c, Γ x 0 b c = 0 := (classical_christoffel_form Γ hΓ).1

private lemma gamma_sp (Γ : Conn) (hΓ : IsClassical Γ) :
    ∀ x i j k, i ≠ 0 → j ≠ 0 → k ≠ 0 → Γ x i j k = 0 :=
  (classical_christoffel_form Γ hΓ).2.1

private lemma riem0_eq_zero (Γ : Conn) (hΓ : IsClassical Γ) (x : E) (b c d : Fin 4) :
    riem Γ x 0 b c d = 0 := by
  have h0 := gamma0 Γ hΓ
  have hfun (e b' : Fin 4) : (fun y : E => Γ y 0 e b') = fun _ => (0 : ℝ) :=
    funext fun y => h0 y e b'
  have hpd (e b' d' : Fin 4) : pd (fun y => Γ y 0 e b') d' x = 0 := by
    rw [pd, hfun e b']; simp
  change
    pd (fun y => Γ y 0 c b) d x - pd (fun y => Γ y 0 d b) c x +
      ∑ e, (Γ x 0 d e * Γ x e c b - Γ x 0 c e * Γ x e d b) = 0
  simp [h0 x, hpd]

private lemma riem_antisym_last (Γ : Conn) (x : E) (a b c d : Fin 4) :
    riem Γ x a b c d = -riem Γ x a b d c := by
  simp only [riem]
  have hsum :
      (∑ e : Fin 4, (Γ x a d e * Γ x e c b - Γ x a c e * Γ x e d b)) =
        -∑ e : Fin 4, (Γ x a c e * Γ x e d b - Γ x a d e * Γ x e c b) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  linarith [hsum]

private lemma riemUp3_of_ne (Γ : Conn) (x : E) (a b c d : Fin 4) (hc : c ≠ 0) :
    riemUp3 Γ x a b c d = riem Γ x a b c d := by
  simp only [riemUp3]
  have hterm (n : Fin 4) :
      riem Γ x a b n d * hh n c = if n = c then riem Γ x a b c d else 0 := by
    simp only [hh]
    by_cases hn : n = c
    · subst hn; simp [hc]
    · simp [hn]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private lemma contDiff_riem_comp (Γ : Conn) (hΓ : ContDiff ℝ ∞ Γ) (a b c d : Fin 4) :
    ContDiff ℝ ∞ (fun x => riem Γ x a b c d) := by
  have hG (p q r : Fin 4) : ContDiff ℝ ∞ (fun x => Γ x p q r) :=
    contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hΓ p) q) r
  have hpd (p q r e : Fin 4) : ContDiff ℝ ∞ (fun x => pd (fun y => Γ y p q r) e x) := by
    have hf := (contDiff_infty_iff_fderiv.1 (hG p q r)).2
    simpa [pd] using ContDiff.clm_apply hf contDiff_const
  have hquad : ContDiff ℝ ∞ (fun x => ∑ e : Fin 4,
      (Γ x a d e * Γ x e c b - Γ x a c e * Γ x e d b)) := by
    refine ContDiff.sum (s := Finset.univ) (fun e _ =>
      ((hG a d e).mul (hG e c b)).sub ((hG a c e).mul (hG e d b)))
  simpa [riem] using ((hpd a c b d).sub (hpd a d b c)).add hquad

private lemma pd2_Gamma_symm (Γ : Conn) (hΓ : ContDiff ℝ ∞ Γ)
    (a b c u v : Fin 4) (z : E) :
    pd (fun y => pd (fun w => Γ w a b c) u y) v z =
      pd (fun y => pd (fun w => Γ w a b c) v y) u z := by
  have hf : ContDiff ℝ ∞ (fun y => Γ y a b c) :=
    contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hΓ a) b) c
  have hfAt : ContDiffAt ℝ ∞ (fun y => Γ y a b c) z := hf.contDiffAt
  have hsymm : IsSymmSndFDerivAt ℝ (fun y => Γ y a b c) z :=
    hfAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]; decide)
  have key (s t : Fin 4) :
      pd (fun y => pd (fun w => Γ w a b c) s y) t z =
        fderiv ℝ (fderiv ℝ (fun w => Γ w a b c)) z (Pi.single t 1) (Pi.single s 1) := by
    simp only [pd]
    have hu : DifferentiableAt ℝ (fderiv ℝ (fun w => Γ w a b c)) z :=
      (hfAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have h := fderiv_clm_apply (c := fderiv ℝ (fun w => Γ w a b c))
      (u := fun _ : E => Pi.single s (1 : ℝ)) hu (differentiableAt_const _)
    have h' := congrArg (fun L : E →L[ℝ] ℝ => L (Pi.single t (1 : ℝ))) h
    simpa [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, fderiv_const, zero_apply] using h'
  rw [key u v, key v u]
  exact hsymm (Pi.single v 1) (Pi.single u 1)

private lemma contDiff_pd_Gamma (Γ : Conn) (hΓ : ContDiff ℝ ∞ Γ)
    (a b c e : Fin 4) : ContDiff ℝ ∞ (fun x => pd (fun y => Γ y a b c) e x) := by
  have hG : ContDiff ℝ ∞ (fun y => Γ y a b c) :=
    contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hΓ a) b) c
  have hf := (contDiff_infty_iff_fderiv.1 hG).2
  simpa [pd] using ContDiff.clm_apply hf contDiff_const

private lemma riem_middle_eq_pd_omega (Γt : Conn) (hΓt : IsClassical Γt)
    (x : E) (i j k : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0) :
    riem Γt x i j 0 k = pd (fun y => Γt y i 0 j) k x := by
  have hΓ0 := gamma0 Γt hΓt
  have hΓsp := gamma_sp Γt hΓt
  have hpd_ikj : pd (fun y => Γt y i k j) 0 x = 0 := by
    have : (fun y => Γt y i k j) = fun _ => (0 : ℝ) :=
      funext fun y => hΓsp y i k j hi hk hj
    rw [pd, this]; simp
  have hquad : (∑ e : Fin 4, (Γt x i k e * Γt x e 0 j - Γt x i 0 e * Γt x e k j)) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : e = 0
    · subst he; simp [hΓ0 x]
    · simp [hΓsp x i k e hi hk he, hΓsp x e k j he hk hj]
  simp only [riem, hpd_ikj, hquad, sub_zero, add_zero]

private lemma omega_spatially_const (Γt : Conn) (ρ : E → ℝ)
    (hΓt : IsClassical Γt) (hcurv : CurvConds Γt ρ)
    (x : E) (i j k : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0) :
    pd (fun y => Γt y i 0 j) k x = 0 := by
  have hR0 : riem Γt x i j 0 k = 0 := by
    have h := hcurv.2.2 x i j 0 k
    have hterm (n : Fin 4) :
        riem Γt x i n 0 k * hh n j = if n = j then riem Γt x i j 0 k else 0 := by
      simp only [hh]
      by_cases hn : n = j
      · subst hn; simp [hj]
      · simp [hn]
    simpa [riemUp2, hterm, Finset.sum_ite_eq', Finset.mem_univ] using h
  rwa [riem_middle_eq_pd_omega Γt hΓt x i j k hi hj hk] at hR0

private lemma F_spatial_expr (Γt : Conn) (hΓt : IsClassical Γt)
    (x : E) (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) :
    riem Γt x i 0 0 j =
      pd (fun y => Γt y i 0 0) j x - pd (fun y => Γt y i 0 j) 0 x -
        ∑ e : Fin 4, Γt x i 0 e * Γt x e 0 j := by
  have hΓ0 := gamma0 Γt hΓt
  have hΓsp := gamma_sp Γt hΓt
  have htors := hΓt.1.2
  have hquad1 : (∑ e : Fin 4, Γt x i j e * Γt x e 0 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : e = 0
    · subst he; simp [hΓ0]
    · simp [hΓsp x i j e hi hj he]
  have hB : pd (fun y => Γt y i j 0) 0 x = pd (fun y => Γt y i 0 j) 0 x := by
    have : (fun y => Γt y i j 0) = (fun y => Γt y i 0 j) :=
      funext fun y => htors y i j 0
    simp [this]
  have hE (e : Fin 4) : Γt x e j 0 = Γt x e 0 j := htors x e j 0
  -- riem = ∂_j Γ^i_00 - ∂_0 Γ^i_j0 + ∑(Γ^i_je Γ^e_00 - Γ^i_0e Γ^e_j0)
  --      = ∂_j Γ^i_00 - ∂_0 Γ^i_0j - ∑ Γ^i_0e Γ^e_0j
  calc riem Γt x i 0 0 j
      = pd (fun y => Γt y i 0 0) j x - pd (fun y => Γt y i j 0) 0 x +
          ∑ e, (Γt x i j e * Γt x e 0 0 - Γt x i 0 e * Γt x e j 0) := by
            simp [riem]
    _ = pd (fun y => Γt y i 0 0) j x - pd (fun y => Γt y i 0 j) 0 x +
          ∑ e, (Γt x i j e * Γt x e 0 0 - Γt x i 0 e * Γt x e 0 j) := by
            simp [hB, hE]
    _ = pd (fun y => Γt y i 0 0) j x - pd (fun y => Γt y i 0 j) 0 x +
          ∑ e, (0 - Γt x i 0 e * Γt x e 0 j) := by
            congr 1
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [show Γt x i j e * Γt x e 0 0 = 0 from ?_]
            · by_cases he : e = 0
              · subst he; simp [hΓ0]
              · simp [hΓsp x i j e hi hj he]
    _ = pd (fun y => Γt y i 0 0) j x - pd (fun y => Γt y i 0 j) 0 x -
          ∑ e, Γt x i 0 e * Γt x e 0 j := by
            simp [Finset.sum_neg_distrib]
            ring

theorem solution (Γt : Conn) (ρ : E → ℝ)
    (hΓt : IsClassical Γt) (_hρ : ContDiff ℝ ∞ ρ) (hcurv : CurvConds Γt ρ)
    (_hform : ∀ x a b c d,
      riem Γt x a b c d =
        tt b * (tt c * riem Γt x a 0 0 d - tt d * riem Γt x a 0 0 c)) :
    let F : E → Fin 4 → Fin 4 → ℝ := fun x a d => riem Γt x a 0 0 d
    ContDiff ℝ ∞ F ∧
      (∀ x d, F x 0 d = 0) ∧ (∀ x a, F x a 0 = 0) ∧
      (∀ x i j, F x i j = F x j i) ∧
      (∀ x i j k, i ≠ 0 → j ≠ 0 → k ≠ 0 →
        pd (fun y => F y i j) k x = pd (fun y => F y i k) j x) ∧
      (∀ x, ∑ i : Fin 4, F x i i = 4 * Real.pi * ρ x) := by
  intro F
  refine ⟨?cont, ?row, ?col, ?sym, ?closed, ?tr⟩
  · exact contDiff_pi.2 fun a => contDiff_pi.2 fun d =>
      contDiff_riem_comp Γt hΓt.1.1 a 0 0 d
  · intro x d; exact riem0_eq_zero Γt hΓt x 0 0 d
  · intro x a
    have h := riem_antisym_last Γt x a 0 0 0
    linarith
  · intro x i j
    by_cases hi : i = 0
    · subst hi
      have h1 := riem0_eq_zero Γt hΓt x 0 0 j
      have h2 : riem Γt x j 0 0 0 = 0 := by
        have := riem_antisym_last Γt x j 0 0 0; linarith
      exact h1.trans h2.symm
    · by_cases hj : j = 0
      · subst hj
        have h1 : riem Γt x i 0 0 0 = 0 := by
          have := riem_antisym_last Γt x i 0 0 0; linarith
        exact h1.trans (riem0_eq_zero Γt hΓt x 0 0 i).symm
      · have hL : riemUp3 Γt x i 0 j 0 = riem Γt x i 0 j 0 :=
          riemUp3_of_ne Γt x i 0 j 0 hj
        have hR : riemUp3 Γt x j 0 i 0 = riem Γt x j 0 i 0 :=
          riemUp3_of_ne Γt x j 0 i 0 hi
        have hsym := hcurv.2.1 x i 0 j 0
        have h1 : riem Γt x i 0 j 0 = -riem Γt x i 0 0 j :=
          riem_antisym_last Γt x i 0 j 0
        have h2 : riem Γt x j 0 i 0 = -riem Γt x j 0 0 i :=
          riem_antisym_last Γt x j 0 i 0
        calc F x i j = riem Γt x i 0 0 j := rfl
          _ = -riem Γt x i 0 j 0 := by linarith [h1]
          _ = -riemUp3 Γt x i 0 j 0 := by rw [hL]
          _ = -riemUp3 Γt x j 0 i 0 := by rw [hsym]
          _ = -riem Γt x j 0 i 0 := by rw [hR]
          _ = riem Γt x j 0 0 i := by linarith [h2]
          _ = F x j i := rfl
  · intro x i j k hi hj hk
    -- Spatial closedness via structure
    have hΓinf : ContDiff ℝ ∞ Γt := hΓt.1.1
    have hG (p q r : Fin 4) : ContDiff ℝ ∞ (fun y => Γt y p q r) :=
      contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hΓinf p) q) r
    have hdiffG (p q r : Fin 4) : Differentiable ℝ (fun y => Γt y p q r) :=
      (hG p q r).differentiable (by simp)
    have hdiffPd (p q r e : Fin 4) :
        Differentiable ℝ (fun y => pd (fun w => Γt w p q r) e y) :=
      (contDiff_pd_Gamma Γt hΓinf p q r e).differentiable (by simp)
    -- Express F
    have hFij (y : E) : riem Γt y i 0 0 j =
        pd (fun w => Γt w i 0 0) j y - pd (fun w => Γt w i 0 j) 0 y -
          ∑ e : Fin 4, Γt y i 0 e * Γt y e 0 j :=
      F_spatial_expr Γt hΓt y i j hi hj
    have hFik (y : E) : riem Γt y i 0 0 k =
        pd (fun w => Γt w i 0 0) k y - pd (fun w => Γt w i 0 k) 0 y -
          ∑ e : Fin 4, Γt y i 0 e * Γt y e 0 k :=
      F_spatial_expr Γt hΓt y i k hi hk
    -- Define component functions
    let A : E → ℝ := fun y => pd (fun w => Γt w i 0 0) j y
    let B : E → ℝ := fun y => pd (fun w => Γt w i 0 j) 0 y
    let Q : E → ℝ := fun y => ∑ e : Fin 4, Γt y i 0 e * Γt y e 0 j
    let Ap : E → ℝ := fun y => pd (fun w => Γt w i 0 0) k y
    let Bp : E → ℝ := fun y => pd (fun w => Γt w i 0 k) 0 y
    let Qp : E → ℝ := fun y => ∑ e : Fin 4, Γt y i 0 e * Γt y e 0 k
    have hEqL : (fun y => riem Γt y i 0 0 j) = fun y => A y - B y - Q y := by
      funext y
      have := hFij y
      dsimp [A, B, Q] at this ⊢
      linarith
    have hEqR : (fun y => riem Γt y i 0 0 k) = fun y => Ap y - Bp y - Qp y := by
      funext y
      have := hFik y
      dsimp [Ap, Bp, Qp] at this ⊢
      linarith
    have dA : DifferentiableAt ℝ A x := (hdiffPd i 0 0 j).differentiableAt
    have dB : DifferentiableAt ℝ B x := (hdiffPd i 0 j 0).differentiableAt
    have dQ : DifferentiableAt ℝ Q x :=
      DifferentiableAt.fun_sum (u := (Finset.univ : Finset (Fin 4)))
        (fun e _ => ((hdiffG i 0 e).differentiableAt).mul ((hdiffG e 0 j).differentiableAt))
    have dAp : DifferentiableAt ℝ Ap x := (hdiffPd i 0 0 k).differentiableAt
    have dBp : DifferentiableAt ℝ Bp x := (hdiffPd i 0 k 0).differentiableAt
    have dQp : DifferentiableAt ℝ Qp x :=
      DifferentiableAt.fun_sum (u := (Finset.univ : Finset (Fin 4)))
        (fun e _ => ((hdiffG i 0 e).differentiableAt).mul ((hdiffG e 0 k).differentiableAt))
    have pd_sub' (f g : E → ℝ) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
        (dir : Fin 4) : pd (fun y => f y - g y) dir x = pd f dir x - pd g dir x := by
      have hfg : (fun y => f y - g y) = f - g := rfl
      simp only [pd, hfg, fderiv_sub hf hg, sub_apply]
    have hL : pd (fun y => riem Γt y i 0 0 j) k x = pd A k x - pd B k x - pd Q k x := by
      rw [hEqL, pd_sub' (fun y => A y - B y) Q (dA.sub dB) dQ k,
        pd_sub' A B dA dB k]
    have hR : pd (fun y => riem Γt y i 0 0 k) j x = pd Ap j x - pd Bp j x - pd Qp j x := by
      rw [hEqR, pd_sub' (fun y => Ap y - Bp y) Qp (dAp.sub dBp) dQp j,
        pd_sub' Ap Bp dAp dBp j]
    have hAeq : pd A k x = pd Ap j x := pd2_Gamma_symm Γt hΓinf i 0 0 j k x
    -- B derivatives vanish by omega spatially const + Clairaut
    have hB0 : pd B k x = 0 := by
      change pd (fun y => pd (fun w => Γt w i 0 j) 0 y) k x = 0
      rw [pd2_Gamma_symm Γt hΓinf i 0 j 0 k x]
      have hzero : (fun y => pd (fun w => Γt w i 0 j) k y) = fun _ => (0 : ℝ) := by
        funext y; exact omega_spatially_const Γt ρ hΓt hcurv y i j k hi hj hk
      rw [pd, hzero]; simp
    have hBp0 : pd Bp j x = 0 := by
      change pd (fun y => pd (fun w => Γt w i 0 k) 0 y) j x = 0
      rw [pd2_Gamma_symm Γt hΓinf i 0 k 0 j x]
      have hzero : (fun y => pd (fun w => Γt w i 0 k) j y) = fun _ => (0 : ℝ) := by
        funext y; exact omega_spatially_const Γt ρ hΓt hcurv y i k j hi hk hj
      rw [pd, hzero]; simp
    -- Q derivatives vanish: each summand is spatially constant
    have hterm0 (m : Fin 4) :
        (fun y => Γt y i 0 0 * Γt y 0 0 m) = fun _ => (0 : ℝ) := by
      funext y; simp [gamma0 Γt hΓt y]
    have pd_mul_omega (e dir m : Fin 4) (he : e ≠ 0) (hm : m ≠ 0) (hdir : dir ≠ 0) :
        pd (fun y => Γt y i 0 e * Γt y e 0 m) dir x = 0 := by
      have hf : DifferentiableAt ℝ (fun y => Γt y i 0 e) x := (hdiffG i 0 e).differentiableAt
      have hg : DifferentiableAt ℝ (fun y => Γt y e 0 m) x := (hdiffG e 0 m).differentiableAt
      have heq : (fun y => Γt y i 0 e * Γt y e 0 m) =
          (fun y => Γt y i 0 e) * (fun y => Γt y e 0 m) := rfl
      simp only [pd, heq, fderiv_mul hf hg, add_apply, smul_apply, smul_eq_mul]
      have h1 : pd (fun y => Γt y i 0 e) dir x = 0 :=
        omega_spatially_const Γt ρ hΓt hcurv x i e dir hi he hdir
      have h2 : pd (fun y => Γt y e 0 m) dir x = 0 :=
        omega_spatially_const Γt ρ hΓt hcurv x e m dir he hm hdir
      simp only [pd] at h1 h2
      simp [h1, h2]
    have hQ0 : pd Q k x = 0 := by
      change pd (fun y => ∑ e : Fin 4, Γt y i 0 e * Γt y e 0 j) k x = 0
      have hφ (e : Fin 4) : DifferentiableAt ℝ (fun y => Γt y i 0 e * Γt y e 0 j) x :=
        ((hdiffG i 0 e).differentiableAt).mul ((hdiffG e 0 j).differentiableAt)
      have hsum := fderiv_fun_sum (u := (Finset.univ : Finset (Fin 4)))
        (A := fun e => fun y => Γt y i 0 e * Γt y e 0 j) (h := fun e _ => hφ e)
      simp only [pd, hsum, FunLike.coe_sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun e _ => ?_
      by_cases he : e = 0
      · subst he
        simp only [pd] at *
        simp [hterm0 j]
      · exact pd_mul_omega e k j he hj hk
    have hQp0 : pd Qp j x = 0 := by
      change pd (fun y => ∑ e : Fin 4, Γt y i 0 e * Γt y e 0 k) j x = 0
      have hφ (e : Fin 4) : DifferentiableAt ℝ (fun y => Γt y i 0 e * Γt y e 0 k) x :=
        ((hdiffG i 0 e).differentiableAt).mul ((hdiffG e 0 k).differentiableAt)
      have hsum := fderiv_fun_sum (u := (Finset.univ : Finset (Fin 4)))
        (A := fun e => fun y => Γt y i 0 e * Γt y e 0 k) (h := fun e _ => hφ e)
      simp only [pd, hsum, FunLike.coe_sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun e _ => ?_
      by_cases he : e = 0
      · subst he
        simp only [pd] at *
        simp [hterm0 k]
      · exact pd_mul_omega e j k he hk hj
    simp only [F, hL, hR, hAeq, hB0, hBp0, hQ0, hQp0]
  · intro x
    have hric := hcurv.1 x 0 0
    simpa [ricci, tt_zero, mul_one, F] using hric
