-- Prove2me | solution 1 for MasulloRH.all_cell_pole_autocorrelation_and_exact_geometric_compensation
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T19:21:25.660981+00:00
-- url     : https://prove2.me/submissions/25c0ab57-b35b-4c80-b923-e9bbcf835703

import Mathlib
open MeasureTheory

theorem solution (L : ℝ) (hL : 0 < L) (m : ℕ) (f : ℝ → ℝ) (hf : Continuous f) :
    let r := Real.exp (-L/2)
    let q := r*r
    let g := fun (k : ℕ) (x : ℝ) => -(r^(k+1))*Real.exp (x/2)
    let first := fun s : ℝ => ∫ x in s..L, g m x * g 0 (x-s)
    let later := fun (k : ℕ) (s : ℝ) =>
      (∫ x in (0:ℝ)..s, g (k+1+m) x * g k (x-s+L)) +
      (∫ x in s..L, g (k+1+m) x * g (k+1) (x-s))
    let test := fun (F : ℝ → ℝ) => ∫ s in (0:ℝ)..L, f s * F s
    (∀ s ∈ Set.Icc 0 L, first s =
        r^m * (Real.exp (-s/2) - q * Real.exp (s/2)) ∧
      (∀ k, later k s = r^m * q^(k+1) * (1-q) * Real.exp (s/2))) ∧
    HasSum (fun k => test (later k))
      (r^m * q * test (fun s => Real.exp (s/2))) ∧
    test first + (∑' k : ℕ, test (later k)) =
      r^m * test (fun s => Real.exp (-s/2)) := by
  intro r q g first later test
  have rpos : 0 < r := Real.exp_pos _
  have rlt : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have qlt : q < 1 := calc
    r*r < 1*1 := mul_lt_mul'' rlt rlt rpos.le rpos.le
    _ = 1 := one_mul 1
  have hshift : r * Real.exp (L/2) = 1 := by
    dsimp [r]
    rw [← Real.exp_add, show -L/2+L/2=0 by ring, Real.exp_zero]
  have hfull : q * Real.exp L = 1 := by
    dsimp [q,r]
    rw [← Real.exp_add, ← Real.exp_add, show -L/2+-L/2+L=0 by ring, Real.exp_zero]
  have hpos (s : ℝ) : Real.exp (-s/2)*Real.exp s = Real.exp (s/2) := by
    rw [← Real.exp_add, show -s/2+s=s/2 by ring]
  have same (k : ℕ) (x s : ℝ) :
      g (k+m) x * g k (x-s) =
      (r^m * q^k * q * Real.exp (-s/2)) * Real.exp x := by
    have he : Real.exp (x/2) * Real.exp ((x-s)/2) = Real.exp (-s/2)*Real.exp x := by
      simp only [← Real.exp_add]
      congr 1 <;> ring
    calc
      _ = (r^m*q^k*q) * (Real.exp (x/2)*Real.exp ((x-s)/2)) := by
        simp only [g,q,pow_add,pow_one,mul_pow]
        ring
      _ = _ := by rw [he]; ring
  have cross (k : ℕ) (x s : ℝ) :
      g (k+1+m) x * g k (x-s+L) =
      (r^m * q^(k+1) * Real.exp (-s/2)) * Real.exp x := by
    have he : Real.exp (x/2) * Real.exp ((x-s+L)/2) =
        Real.exp (L/2) * (Real.exp (-s/2)*Real.exp x) := by
      simp only [← Real.exp_add]
      congr 1 <;> ring
    calc
      _ = (r^m*q^(k+1)*r) * (Real.exp (x/2)*Real.exp ((x-s+L)/2)) := by
        simp only [g,q,pow_add,pow_one,mul_pow]
        ring
      _ = r^m*q^(k+1)*(r*Real.exp (L/2))*(Real.exp (-s/2)*Real.exp x) := by
        rw [he]; ring
      _ = _ := by rw [hshift]; ring
  have fshape (s : ℝ) : first s = r^m * (Real.exp (-s/2)-q*Real.exp (s/2)) := by
    have ha (x : ℝ) : g m x * g 0 (x-s) =
        (r^m * q * Real.exp (-s/2)) * Real.exp x := by
      simpa only [Nat.zero_add,pow_zero,mul_one] using same 0 x s
    dsimp only [first]
    simp_rw [ha]
    rw [intervalIntegral.integral_const_mul, integral_exp]
    linear_combination r^m*Real.exp (-s/2)*hfull - r^m*q*hpos s
  have lshape (k : ℕ) (s : ℝ) : later k s = r^m*q^(k+1)*(1-q)*Real.exp (s/2) := by
    dsimp only [later]
    simp_rw [cross, same]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_exp, integral_exp, Real.exp_zero]
    linear_combination r^m*q^(k+1)*Real.exp (-s/2)*hfull +
      r^m*q^(k+1)*(1-q)*hpos s
  let plus := test (fun s => Real.exp (s/2))
  let minus := test (fun s => Real.exp (-s/2))
  have ft : test first = r^m*(minus-q*plus) := by
    dsimp only [test,minus,plus]
    simp_rw [fshape]
    have hr (s : ℝ) : f s*(r^m*(Real.exp (-s/2)-q*Real.exp (s/2))) =
        r^m*(f s*Real.exp (-s/2)) - (r^m*q)*(f s*Real.exp (s/2)) := by ring
    simp_rw [hr]
    have cm : Continuous (fun s : ℝ => r^m*(f s*Real.exp (-s/2))) := by fun_prop
    have cp : Continuous (fun s : ℝ => (r^m*q)*(f s*Real.exp (s/2))) := by fun_prop
    rw [intervalIntegral.integral_sub (cm.intervalIntegrable _ _) (cp.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  have ltst (k : ℕ) : test (later k) = q^k*(r^m*q*(1-q)*plus) := by
    dsimp only [test,plus]
    simp_rw [lshape]
    have hr (s : ℝ) : f s*(r^m*q^(k+1)*(1-q)*Real.exp (s/2)) =
        (q^k*(r^m*q*(1-q)))*(f s*Real.exp (s/2)) := by rw [pow_succ]; ring
    simp_rw [hr]
    rw [intervalIntegral.integral_const_mul]
    ring
  have tail : HasSum (fun k => test (later k)) (r^m*q*plus) := by
    simp_rw [ltst]
    have hs := (hasSum_geometric_of_lt_one (mul_nonneg rpos.le rpos.le) qlt).mul_right
      (r^m*q*(1-q)*plus)
    have hn : 1-q ≠ 0 := ne_of_gt (sub_pos.mpr qlt)
    have ev : (1-q)⁻¹*(r^m*q*(1-q)*plus) = r^m*q*plus := by field_simp
    exact ev ▸ hs
  refine ⟨fun s _ => ⟨fshape s, fun k => lshape k s⟩,tail,?_⟩
  rw [tail.tsum_eq,ft]
  change r^m*(minus-q*plus)+r^m*q*plus=r^m*minus
  ring
