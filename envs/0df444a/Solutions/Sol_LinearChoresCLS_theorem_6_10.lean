-- Prove2me | solution 1 for LinearChoresCLS.theorem_6_10
-- status  : ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T20:52:45.854696+00:00
-- url     : https://prove2.me/submissions/86028029-a070-4d1f-ad24-6c433bf30b94

import Definitions.Def_LinearChoresCLS_Remainders
import Definitions.Def_LinearChoresCLS_RightDeriv

open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash Filter Set Topology

private theorem fromRight {f : ℝ → ℝ} {d : ℝ} :
    HasRightDerivAt0 f d ↔ HasDerivWithinAt f d (Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have he : slope f 0 = (fun h : ℝ => h⁻¹ • (f h-f 0)) := by funext h; simp [slope_def_module]
  rw [he]; rfl

open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash Set Filter Topology

private noncomputable def remTerm (b t u : ℝ) : ℝ := b*(Real.log (1+t*u)-t*u)

private theorem rem_deriv {b t u : ℝ} (ht : 0<t) (hu : 0≤u) :
    HasDerivAt (remTerm b t) (b*(t/(1+t*u)-t)) u := by
  have h : HasDerivAt (fun v : ℝ => t*v) t u := by
    simpa only [id_eq,mul_one] using! (hasDerivAt_id u).const_mul t
  exact (((h.const_add 1).log (show 1+t*u ≠ 0 by positivity)).sub h).const_mul b

private theorem size_coeff {n : ℕ} (P : Quadratic n) (i : Fin n) :
    |lam P * (P.c i:ℝ)| ≤ 1/(2*((n:ℝ)+1)) := by
  let A := ∑ j, ∑ k, |(P.Q j k:ℝ)|
  let C := ∑ j, |(P.c j:ℝ)|
  have ha : 0 ≤ A := by dsimp [A]; positivity
  have hc : |(P.c i:ℝ)| ≤ C := single_le_sum (fun k _ => abs_nonneg (P.c k : ℝ)) (mem_univ i)
  have hl : 0 < lam P := by unfold lam; positivity
  rw [abs_mul,abs_of_pos hl]
  calc
    _ ≤ lam P*(1+A+C) := mul_le_mul_of_nonneg_left (by linarith) hl.le
    _ = _ := by dsimp [lam,A,C]; field_simp

private theorem diff_one {n : ℕ} (P : Quadratic n) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) (h : ℝ) :
    Rlin P t (x+h • Pi.single i (1:ℝ))-Rlin P t x =
      remTerm (alpha P t / t * (P.c i:ℝ)) t (x i+h) - remTerm (alpha P t / t * (P.c i:ℝ)) t (x i) := by
  classical
  unfold Rlin; rw [← sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp [remTerm]
  · intro j _ hj; simp [Pi.single_apply,hj,Ne.symm hj]
  · simp

theorem solution {n : ℕ} (P : Quadratic n) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (∀ x : Fin n → ℝ, InCube x →
      alpha P t / t * ∑ j, cExt P j * Real.log (basicPrice t x j) =
        alpha P t * ∑ i, (P.c i : ℝ) * x i + Rlin P t x) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single ℓ (1 : ℝ)) →
      |Rlin P t (x + h • Pi.single ℓ (1 : ℝ)) - Rlin P t x| ≤ t ^ 3 / (2 * (n + 1)) * |h|) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (s : Bool), InCube x → FeasibleCoordDir x ℓ s →
      ∃ D : ℝ, HasRightDerivAt0 (fun h => Rlin P t (x + h • coordDir ℓ s)) D ∧
        |D| ≤ t ^ 3 / (2 * (n + 1))) := by
  classical
  let b := fun i => alpha P t/t*(P.c i:ℝ)
  let K := t^3/(2*((n:ℝ)+1))
  have bound (i : Fin n) (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : |b i*(t/(1+t*u)-t)| ≤ K := by
    have h0 := hu.1; have h1 := hu.2
    have hd : 0 < 1+t*u := by positivity
    have he : b i*(t/(1+t*u)-t) = -(lam P*(P.c i:ℝ)) * (t^3*(u/(1+t*u))) := by
      dsimp [b,alpha]; field_simp; ring
    rw [he,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0 ≤ t^3*(u/(1+t*u)))]
    have hu' : u/(1+t*u) ≤ 1 := (div_le_one hd).mpr (by nlinarith [mul_nonneg ht.le h0])
    calc
      _ ≤ (1/(2*((n:ℝ)+1)))*(t^3*1) := mul_le_mul (size_coeff P i) (mul_le_mul_of_nonneg_left hu' (by positivity)) (by positivity) (by positivity)
      _ = _ := by dsimp [K]; ring
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have pos (j : Fin (n+1)) : 0 ≤ xExt x j :=
      Fin.cases (by simp [xExt]) (fun a => by simpa [xExt] using (hx a).1) j
    have hb : 0 ≤ xbar x := div_nonneg (sum_nonneg (fun j _ => pos j)) (by positivity)
    have hp (j : Fin (n+1)) : Real.log (basicPrice t x j) = Real.log (1+t*xExt x j) - Real.log (1+t*xbar x) := by
      have := pos j
      exact Real.log_div (by positivity) (by positivity)
    rw [Fin.sum_univ_succ (fun j : Fin (n+1) => cExt P j * Real.log (basicPrice t x j))]
    simp only [hp,cExt,xExt,Fin.cons_succ,Fin.cons_zero,mul_zero,add_zero,Real.log_one,zero_sub,Rlin]
    simp only [mul_sub,neg_mul,mul_neg,neg_neg,Finset.sum_mul,Finset.sum_sub_distrib]
    rw [show ∀ a b : ℝ, a+(b-a)=b by intros; ring]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    field_simp; ring
  · intro x i h hx hy
    have hi : x i+h ∈ Icc (0:ℝ) 1 := by simpa using hy i
    have hh := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u (hu : u ∈ Icc (0:ℝ) 1) => (rem_deriv (b := b i) ht hu.1).hasDerivWithinAt)
      (fun u hu => by simpa only [Real.norm_eq_abs] using bound i u hu) (hx i) hi
    rw [diff_one]; simpa only [Real.norm_eq_abs,add_sub_cancel_left] using hh
  · intro x i s hx _
    let v : ℝ := if s then 1 else -1
    have hline : (fun h : ℝ => Rlin P t (x+h • coordDir i s)) =
        (fun h : ℝ => Rlin P t x + (remTerm (b i) t (x i+h*v) - remTerm (b i) t (x i))) := by
      funext h
      have hv : h • coordDir i s = (h*v) • Pi.single i (1:ℝ) := by
        ext j; by_cases he : i=j <;> simp [coordDir,v,Pi.single_apply,he,Ne.symm]
      rw [hv]; linarith [diff_one P t x i (h*v)]
    have aff : HasDerivAt (fun h : ℝ => x i+h*v) v 0 := by
      simpa only [one_mul,id_eq] using! (((hasDerivAt_id (0:ℝ)).mul_const v).const_add (x i))
    have hd : HasDerivAt (remTerm (b i) t) (b i*(t/(1+t*x i)-t)) ((fun h : ℝ => x i+h*v) 0) := by
      simpa only [zero_mul,add_zero] using! (rem_deriv (b := b i) ht (hx i).1)
    have hd' := (((hd.comp 0 aff).sub_const (remTerm (b i) t (x i))).const_add (Rlin P t x))
    refine ⟨(b i*(t/(1+t*x i)-t))*v,?_,?_⟩
    · rw [hline]; exact fromRight.mpr hd'.hasDerivWithinAt
    · rw [abs_mul]; have he : |v| = 1 := by cases s <;> norm_num [v]
      rw [he,mul_one]; exact bound i (x i) (hx i)
