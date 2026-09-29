-- Prove2me | solution 1 for NoetherIVP.noether_theorem_I
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T16:14:50.295931+00:00
-- url     : https://prove2.me/submissions/357d656d-2017-4fbd-8aae-dfda032a8e09

import Mathlib
import Definitions.Def_NoetherIVP_core

open Finset NoetherIVP

namespace NoetherAux

/-- `dirD` obeys the Leibniz rule. -/
private lemma dirD_mul {n : ℕ} (l : Fin n) (g h : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) :
    dirD l (fun y => g y * h y) x = dirD l g x * h x + g x * dirD l h x := by
  unfold dirD
  rw [fderiv_fun_mul hg hh]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  ring

/-- `dirD` commutes with finite sums. -/
private lemma dirD_sum {n : ℕ} {ι : Type*} (s : Finset ι) (l : Fin n)
    (g : ι → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) x) :
    dirD l (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, dirD l (g i) x := by
  unfold dirD
  rw [fderiv_fun_sum hg]
  simp

private lemma dirD_neg {n : ℕ} (l : Fin n) (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    dirD l (fun y => -g y) x = -dirD l g x := by
  unfold dirD
  rw [fderiv_fun_neg]
  simp

private lemma dirD_sub {n : ℕ} (l : Fin n) (g h : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) :
    dirD l (fun y => g y - h y) x = dirD l g x - dirD l h x := by
  unfold dirD
  rw [fderiv_fun_sub hg hh]
  simp

/-- The components of the boundary vector `A` are differentiable where the momenta and the
variation are. -/
private lemma differentiableAt_bdryA {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (x : Fin n → ℝ) (l : Fin n)
    (hdu : ∀ i : Fin m, DifferentiableAt ℝ (fun y => du y i) x)
    (hmom : ∀ (l : Fin n) (i : Fin m), DifferentiableAt ℝ (mom f u l i) x) :
    DifferentiableAt ℝ (fun y => bdryA f u du y l) x := by
  unfold bdryA
  exact (DifferentiableAt.fun_sum fun i _ => (hmom l i).fun_mul (hdu i)).neg

/-- The divergence is additive on differentiable vector fields. -/
private lemma divg_sub {n : ℕ} (A B : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ)
    (hA : ∀ l : Fin n, DifferentiableAt ℝ (fun y => A y l) x)
    (hB : ∀ l : Fin n, DifferentiableAt ℝ (fun y => B y l) x) :
    divg (fun y l => A y l - B y l) x = divg A x - divg B x := by
  unfold divg
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => dirD_sub l (fun y => A y l) (fun y => B y l) x (hA l) (hB l)

/-- The divergence of the boundary vector `A` of equation (3), expanded by the Leibniz rule. -/
private lemma divg_bdryA {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (x : Fin n → ℝ)
    (hdu : ∀ i : Fin m, DifferentiableAt ℝ (fun y => du y i) x)
    (hmom : ∀ (l : Fin n) (i : Fin m), DifferentiableAt ℝ (mom f u l i) x) :
    divg (bdryA f u du) x
      = -∑ l : Fin n, ∑ i : Fin m,
          (dirD l (mom f u l i) x * du x i + mom f u l i x * dirD l (fun y => du y i) x) := by
  unfold divg bdryA
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [dirD_neg l (fun y => ∑ i : Fin m, mom f u l i y * du y i) x]
  congr 1
  rw [dirD_sum Finset.univ l (fun i y => mom f u l i y * du y i) x
    (fun i _ => (hmom l i).mul (hdu i))]
  exact Finset.sum_congr rfl fun i _ =>
    dirD_mul l (mom f u l i) (fun y => du y i) x (hmom l i) (hdu i)

/-- Noether (1918), eq. (3): the central identity of the calculus of variations. -/
lemma central_identity {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (x : Fin n → ℝ)
    (hdu : ∀ i : Fin m, DifferentiableAt ℝ (fun y => du y i) x)
    (hmom : ∀ (l : Fin n) (i : Fin m), DifferentiableAt ℝ (mom f u l i) x) :
    ∑ i : Fin m, lagrangeExpr f u i x * du x i
      = varF f u du x + divg (bdryA f u du) x := by
  rw [divg_bdryA f u du x hdu hmom]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin m)))]
  unfold varF lagrangeExpr
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpdV : ∀ l : Fin n, pdV f l i x (u x) (jac u x) = mom f u l i x := fun _ => rfl
  simp only [hpdV]
  rw [sub_mul, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

/-- Noether (1918), eq. (12). -/
lemma div_identity {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (dx : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ)
    (hdu : ∀ i : Fin m, DifferentiableAt ℝ (fun y => du y i) x)
    (hmom : ∀ (l : Fin n) (i : Fin m), DifferentiableAt ℝ (mom f u l i) x)
    (hfdx : ∀ l : Fin n, DifferentiableAt ℝ (fun y => lagr f u y * dx y l) x)
    (hinv : varF f u du x + divg (fun z l => lagr f u z * dx z l) x = 0) :
    ∑ i : Fin m, lagrangeExpr f u i x * du x i = divg (curB f u du dx) x := by
  have hB : divg (curB f u du dx) x
      = divg (bdryA f u du) x - divg (fun z l => lagr f u z * dx z l) x :=
    divg_sub (bdryA f u du) (fun z l => lagr f u z * dx z l) x
      (fun l => differentiableAt_bdryA f u du x l hdu hmom) hfdx
  rw [hB, central_identity f u du x hdu hmom]
  linarith [hinv]

end NoetherAux

theorem solution {n m rho : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u : (Fin n → ℝ) → Fin m → ℝ) (Du : Fin rho → (Fin n → ℝ) → Fin m → ℝ)
    (Dx : Fin rho → (Fin n → ℝ) → Fin n → ℝ)
    (hdu : ∀ (r : Fin rho) (i : Fin m) (x : Fin n → ℝ),
      DifferentiableAt ℝ (fun y => deltaU u (Du r) (Dx r) y i) x)
    (hmom : ∀ (l : Fin n) (i : Fin m) (x : Fin n → ℝ),
      DifferentiableAt ℝ (mom f u l i) x)
    (hfdx : ∀ (r : Fin rho) (l : Fin n) (x : Fin n → ℝ),
      DifferentiableAt ℝ (fun y => lagr f u y * Dx r y l) x)
    (hinv : ∀ (r : Fin rho) (x : Fin n → ℝ),
      varF f u (deltaU u (Du r) (Dx r)) x
        + divg (fun z l => lagr f u z * Dx r z l) x = 0) :
    ∀ (r : Fin rho) (x : Fin n → ℝ),
      (∑ i : Fin m, lagrangeExpr f u i x * deltaU u (Du r) (Dx r) x i)
        = divg (curB f u (deltaU u (Du r) (Dx r)) (Dx r)) x := fun r x =>
  NoetherAux.div_identity f u (deltaU u (Du r) (Dx r)) (Dx r) x (fun i => hdu r i x)
    (fun l i => hmom l i x) (fun l => hfdx r l x) (hinv r x)
