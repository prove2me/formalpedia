-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.clearedFE_of_sum_mul_of_termwise_clearedFE
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/cdf4e032-b59b-50ef-9230-45e771545d07

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_clearedFE_of_sum_mul_of_termwise_clearedFE

set_option autoImplicit false

open LaurentPolynomial

namespace F8Kit

theorem cpow_ne_zero' (N : ℕ) (hN : (N : ℂ) ≠ 0) (s : ℂ) : (N : ℂ) ^ s ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl hN)

noncomputable def u (N : ℕ) (hN : (N : ℂ) ≠ 0) (s : ℂ) : ℂˣ := Units.mk0 ((N : ℂ) ^ s) (cpow_ne_zero' N hN s)

noncomputable def ev (N : ℕ) (hN : (N : ℂ) ≠ 0) (s : ℂ) : ℂ[T;T⁻¹] →+* ℂ := eval₂ (RingHom.id ℂ) (u N hN s)

variable (N : ℕ) (hN : (N : ℂ) ≠ 0)

theorem ev_T (s : ℂ) (n : ℤ) : ev N hN s (T n) = (N : ℂ) ^ ((n : ℂ) * s) := by
  rw [ev, eval₂_T, Units.val_zpow_eq_zpow_val, u, Units.val_mk0, Complex.cpow_int_mul]

theorem ev_C (s : ℂ) (a : ℂ) : ev N hN s (C a) = a := by
  rw [ev, eval₂_C]; rfl

theorem ev_pos (s : ℂ) (R : Polynomial ℂ) : ev N hN s (Polynomial.toLaurent R) = R.eval ((N : ℂ) ^ s) := by
  rw [ev, eval₂_toLaurent, u, Units.val_mk0]; rfl

theorem eval₂_invert {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : Sˣ) (g : R[T;T⁻¹]) :
    eval₂ f x (invert g) = eval₂ f x⁻¹ g := by
  induction g using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | C_mul_T n a => rw [map_mul, invert_C, invert_T, eval₂_C_mul_T, eval₂_C_mul_T, zpow_neg, inv_zpow]

theorem ev_neg (s : ℂ) (R : Polynomial ℂ) :
    ev N hN s (invert (Polynomial.toLaurent R)) = R.eval ((N : ℂ) ^ (-s)) := by
  rw [ev, eval₂_invert, eval₂_toLaurent, Units.val_inv_eq_inv_val, u, Units.val_mk0, ← Complex.cpow_neg]; rfl

theorem invert_invert (g : ℂ[T;T⁻¹]) : invert (invert g) = g := involutive_invert g

theorem infinite_image_cpow (hN1 : 1 < N) (σ : ℝ) :
    Set.Infinite ((fun t : ℝ => (N : ℂ) ^ ((t : ℝ) : ℂ)) '' Set.Ioi σ) := by
  have hN1r : (1 : ℝ) < N := by exact_mod_cast hN1
  refine (Set.Ioi_infinite σ).image fun t₁ _ t₂ _ ht => ?_
  have h1 : ((N : ℝ) ^ (t₁ : ℝ) : ℝ) = (N : ℝ) ^ (t₂ : ℝ) := by
    have := congrArg Complex.re ht
    rwa [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_cpow (by positivity),
      ← Complex.ofReal_cpow (by positivity), Complex.ofReal_re, Complex.ofReal_re] at this
  have hsm : StrictMono (fun t : ℝ => (N : ℝ) ^ t) := fun y z h => (Real.rpow_lt_rpow_left_iff hN1r).mpr h
  exact hsm.injective h1

theorem eq_zero_of_ev (hN1 : 1 < N) (g : ℂ[T;T⁻¹]) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → ev N hN s g = 0) : g = 0 := by
  obtain ⟨n, g', hg'⟩ := exists_T_pow g
  have hroot : ∀ z ∈ (fun t : ℝ => (N : ℂ) ^ ((t : ℝ) : ℂ)) '' Set.Ioi σ, g'.IsRoot z := by
    rintro z ⟨t, ht, rfl⟩
    rw [Polynomial.IsRoot, ← ev_pos N hN, hg', map_mul, h (t : ℂ) (by simpa using ht), zero_mul]
  have hinf : Set.Infinite {z : ℂ | g'.IsRoot z} := (infinite_image_cpow N hN1 σ).mono hroot
  have hg'0 : g' = 0 := Polynomial.eq_zero_of_infinite_isRoot g' hinf
  have : g * T n = 0 := by rw [← hg', hg'0, map_zero]
  exact (mul_eq_zero.mp this).resolve_right (isUnit_T n).ne_zero

theorem eq_of_ev (hN1 : 1 < N) (g g' : ℂ[T;T⁻¹]) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → ev N hN s g = ev N hN s g') : g = g' := by
  refine sub_eq_zero.mp (eq_zero_of_ev N hN hN1 _ σ fun s hs => ?_)
  rw [map_sub, h s hs, sub_self]

theorem toLaurent_invert_ne_zero (R : Polynomial ℂ) (hR : R ≠ 0) : invert (Polynomial.toLaurent R) ≠ 0 := by
  intro h
  have : Polynomial.toLaurent R = 0 := by
    have := congrArg invert h
    rwa [invert_invert, map_zero] at this
  exact hR (Polynomial.toLaurent_eq_zero.mp this)

noncomputable def pl (R : Polynomial ℂ) : ℂ[T;T⁻¹] := Polynomial.toLaurent R

noncomputable def mi (R : Polynomial ℂ) : ℂ[T;T⁻¹] := invert (Polynomial.toLaurent R)

theorem ev_pl (s : ℂ) (R : Polynomial ℂ) : ev N hN s (pl R) = R.eval ((N : ℂ) ^ s) := ev_pos N hN s R
theorem ev_mi (s : ℂ) (R : Polynomial ℂ) : ev N hN s (mi R) = R.eval ((N : ℂ) ^ (-s)) := ev_neg N hN s R
theorem invert_mi (R : Polynomial ℂ) : invert (mi R) = pl R := invert_invert _
theorem invert_pl (R : Polynomial ℂ) : invert (pl R) = mi R := rfl
theorem mi_ne_zero (R : Polynomial ℂ) (hR : R ≠ 0) : mi R ≠ 0 := toLaurent_invert_ne_zero R hR
theorem pl_ne_zero (R : Polynomial ℂ) (hR : R ≠ 0) : pl R ≠ 0 := Polynomial.toLaurent_ne_zero.mpr hR
theorem invert_ne_zero (g : ℂ[T;T⁻¹]) (hg : g ≠ 0) : invert g ≠ 0 := by
  intro h
  apply hg
  have := congrArg invert h
  rwa [invert_invert, map_zero] at this

end F8Kit

open F8Kit

theorem solution
    (N : ℕ) (hN : 1 < N)
    (ι κ : Type) [Fintype ι] [Fintype κ]
    (c cD ΓA ΓZ Γ : ℂ) (kD kA kZ k : ℤ) (hΓ : Γ = cD * ΓA * ΓZ) (hk : k = kD + kA + kZ)
    (Ψ Ψd : ℂ → ℂ) (A Ad Z Zd : ι → κ → ℂ → ℂ)
    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ) (hQ : Q ≠ 0) (hQd : Qd ≠ 0)
    (hrat : (∀ s : ℂ, σ₂ < s.re → Ψ s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))))
    (hratd : (∀ s : ℂ, σ₃ < s.re → Ψd s * Qd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))))
    (hsum : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Ψ s = c * ∑ i, ∑ j, A i j s * Z i j s)
    (hsumd : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Ψd s = c * (cD * (N : ℂ) ^ ((kD : ℂ) * s) * ∑ i, ∑ j, Ad i j s * Zd i j s))
    (hA : ∀ (i : ι) (j : κ), ∃ (PA PAd QA QAd : Polynomial ℂ) (mA mAd : ℤ) (σA σAd : ℝ), QA ≠ 0 ∧ QAd ≠ 0 ∧
      (∀ s : ℂ, σA < s.re → A i j s * QA.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mA : ℂ) * s) * PA.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σAd < s.re → Ad i j s * QAd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mAd : ℂ) * s) * PAd.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((mAd : ℂ) * s) * PAd.eval ((N : ℂ) ^ (-s))) *
            QA.eval ((N : ℂ) ^ s) =
          ((Polynomial.C ΓA).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((kA : ℂ) * s)) *
            ((N : ℂ) ^ ((mA : ℂ) * (-s)) * PA.eval ((N : ℂ) ^ s)) *
            QAd.eval ((N : ℂ) ^ (-s))))
    (hZ : ∀ (i : ι) (j : κ), ∃ (PZ PZd QZ QZd : Polynomial ℂ) (mZ mZd : ℤ) (σZ σZd : ℝ), QZ ≠ 0 ∧ QZd ≠ 0 ∧
      (∀ s : ℂ, σZ < s.re → Z i j s * QZ.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mZ : ℂ) * s) * PZ.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σZd < s.re → Zd i j s * QZd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mZd : ℂ) * s) * PZd.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((mZd : ℂ) * s) * PZd.eval ((N : ℂ) ^ (-s))) *
            QZ.eval ((N : ℂ) ^ s) =
          ((Polynomial.C ΓZ).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((kZ : ℂ) * s)) *
            ((N : ℂ) ^ ((mZ : ℂ) * (-s)) * PZ.eval ((N : ℂ) ^ s)) *
            QZd.eval ((N : ℂ) ^ (-s)))) :
    ∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C Γ).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((k : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) *
            Qd.eval ((N : ℂ) ^ (-s)) := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  subst hΓ hk
  choose PA PAd QA QAd mA mAd σA σAd hQA hQAd hArat hAdrat hAfe using hA
  choose PZ PZd QZ QZd mZ mZd σZ σZd hQZ hQZd hZrat hZdrat hZfe using hZ
  obtain ⟨σ₀, hsum⟩ := hsum
  obtain ⟨σ₁, hsumd⟩ := hsumd

  have hsum' : ∀ s : ℂ, σ₀ < s.re → Ψ s = c * ∑ p : ι × κ, A p.1 p.2 s * Z p.1 p.2 s := by
    intro s hs
    rw [hsum s hs, ← Finset.univ_product_univ, Finset.sum_product]
  have hsumd' : ∀ s : ℂ, σ₁ < s.re →
      Ψd s = c * (cD * (N : ℂ) ^ ((kD : ℂ) * s) * ∑ p : ι × κ, Ad p.1 p.2 s * Zd p.1 p.2 s) := by
    intro s hs
    rw [hsumd s hs, ← Finset.univ_product_univ, Finset.sum_product]

  obtain ⟨σS, hS⟩ : ∃ σS : ℝ, ∀ s : ℂ, σS < s.re →
      (σ₂ < s.re ∧ σ₃ < s.re ∧ σ₀ < s.re ∧ σ₁ < s.re) ∧
      ∀ p : ι × κ, σA p.1 p.2 < s.re ∧ σAd p.1 p.2 < s.re ∧ σZ p.1 p.2 < s.re ∧ σZd p.1 p.2 < s.re := by
    refine ⟨|σ₂| + |σ₃| + |σ₀| + |σ₁| +
      ∑ p : ι × κ, (|σA p.1 p.2| + |σAd p.1 p.2| + |σZ p.1 p.2| + |σZd p.1 p.2|), fun s hs => ?_⟩
    have h0 : 0 ≤ ∑ p : ι × κ, (|σA p.1 p.2| + |σAd p.1 p.2| + |σZ p.1 p.2| + |σZd p.1 p.2|) :=
      Finset.sum_nonneg fun p _ => by positivity
    have a2 := le_abs_self σ₂
    have a3 := le_abs_self σ₃
    have a0 := le_abs_self σ₀
    have a1 := le_abs_self σ₁
    have b2 := abs_nonneg σ₂
    have b3 := abs_nonneg σ₃
    have b0 := abs_nonneg σ₀
    have b1 := abs_nonneg σ₁
    refine ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, fun p => ?_⟩
    have hp : |σA p.1 p.2| + |σAd p.1 p.2| + |σZ p.1 p.2| + |σZd p.1 p.2| ≤
        ∑ p : ι × κ, (|σA p.1 p.2| + |σAd p.1 p.2| + |σZ p.1 p.2| + |σZd p.1 p.2|) :=
      Finset.single_le_sum (f := fun q : ι × κ => |σA q.1 q.2| + |σAd q.1 q.2| + |σZ q.1 q.2| + |σZd q.1 q.2|)
        (fun q _ => by positivity) (Finset.mem_univ p)
    have c1 := le_abs_self (σA p.1 p.2)
    have c2 := le_abs_self (σAd p.1 p.2)
    have c3 := le_abs_self (σZ p.1 p.2)
    have c4 := le_abs_self (σZd p.1 p.2)
    have d1 := abs_nonneg (σA p.1 p.2)
    have d2 := abs_nonneg (σAd p.1 p.2)
    have d3 := abs_nonneg (σZ p.1 p.2)
    have d4 := abs_nonneg (σZd p.1 p.2)
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

  obtain ⟨DL, hDL⟩ : ∃ DL : ℂ[T;T⁻¹], DL = ∏ p : ι × κ, (mi (QA p.1 p.2) * mi (QZ p.1 p.2)) := ⟨_, rfl⟩
  obtain ⟨Dp, hDp⟩ : ∃ Dp : ι × κ → ℂ[T;T⁻¹],
      Dp = fun p => ∏ q ∈ Finset.univ.erase p, (mi (QA q.1 q.2) * mi (QZ q.1 q.2)) := ⟨_, rfl⟩
  obtain ⟨DdL, hDdL⟩ : ∃ DdL : ℂ[T;T⁻¹], DdL = ∏ p : ι × κ, (mi (QAd p.1 p.2) * mi (QZd p.1 p.2)) := ⟨_, rfl⟩
  obtain ⟨Ddp, hDdp⟩ : ∃ Ddp : ι × κ → ℂ[T;T⁻¹],
      Ddp = fun p => ∏ q ∈ Finset.univ.erase p, (mi (QAd q.1 q.2) * mi (QZd q.1 q.2)) := ⟨_, rfl⟩
  have hDsplit : ∀ p : ι × κ, DL = mi (QA p.1 p.2) * mi (QZ p.1 p.2) * Dp p := by
    intro p
    rw [hDL, hDp]
    exact (Finset.mul_prod_erase Finset.univ (fun q : ι × κ => mi (QA q.1 q.2) * mi (QZ q.1 q.2))
      (Finset.mem_univ p)).symm
  have hDdsplit : ∀ p : ι × κ, DdL = mi (QAd p.1 p.2) * mi (QZd p.1 p.2) * Ddp p := by
    intro p
    rw [hDdL, hDdp]
    exact (Finset.mul_prod_erase Finset.univ (fun q : ι × κ => mi (QAd q.1 q.2) * mi (QZd q.1 q.2))
      (Finset.mem_univ p)).symm
  have hDL0 : DL ≠ 0 := by
    rw [hDL]
    exact Finset.prod_ne_zero_iff.mpr fun p _ =>
      mul_ne_zero (mi_ne_zero _ (hQA p.1 p.2)) (mi_ne_zero _ (hQZ p.1 p.2))
  have hDdL0 : DdL ≠ 0 := by
    rw [hDdL]
    exact Finset.prod_ne_zero_iff.mpr fun p _ =>
      mul_ne_zero (mi_ne_zero _ (hQAd p.1 p.2)) (mi_ne_zero _ (hQZd p.1 p.2))

  have FA : ∀ p : ι × κ, T (mAd p.1 p.2) * mi (PAd p.1 p.2) * pl (QA p.1 p.2) =
      C ΓA * T kA * T (-(mA p.1 p.2)) * pl (PA p.1 p.2) * mi (QAd p.1 p.2) := by
    intro p
    refine eq_of_ev N hN0 hN _ _ 0 fun s _ => ?_
    simp only [map_mul, ev_T, ev_C, ev_pl, ev_mi]
    have h := hAfe p.1 p.2 s
    rw [Polynomial.eval_one, Polynomial.eval_C, one_mul] at h
    rw [show (((-(mA p.1 p.2) : ℤ)) : ℂ) * s = ((mA p.1 p.2 : ℤ) : ℂ) * -s by push_cast; ring]
    linear_combination h
  have FZ : ∀ p : ι × κ, T (mZd p.1 p.2) * mi (PZd p.1 p.2) * pl (QZ p.1 p.2) =
      C ΓZ * T kZ * T (-(mZ p.1 p.2)) * pl (PZ p.1 p.2) * mi (QZd p.1 p.2) := by
    intro p
    refine eq_of_ev N hN0 hN _ _ 0 fun s _ => ?_
    simp only [map_mul, ev_T, ev_C, ev_pl, ev_mi]
    have h := hZfe p.1 p.2 s
    rw [Polynomial.eval_one, Polynomial.eval_C, one_mul] at h
    rw [show (((-(mZ p.1 p.2) : ℤ)) : ℂ) * s = ((mZ p.1 p.2 : ℤ) : ℂ) * -s by push_cast; ring]
    linear_combination h

  have L1 : T m * mi P * DL = C c * mi Q * ∑ p : ι × κ,
      T (mA p.1 p.2) * T (mZ p.1 p.2) * mi (PA p.1 p.2) * mi (PZ p.1 p.2) * Dp p := by
    refine eq_of_ev N hN0 hN _ _ σS fun s hs => ?_
    obtain ⟨⟨h2, -, h0, -⟩, hp⟩ := hS s hs
    simp only [map_mul, map_sum, ev_T, ev_C, ev_mi]
    rw [← hrat s h2, hsum' s h0, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨hpA, -, hpZ, -⟩ := hp p
    have ha := hArat p.1 p.2 s hpA
    have hz := hZrat p.1 p.2 s hpZ
    rw [hDsplit p]
    simp only [map_mul, ev_mi]
    linear_combination (c * Q.eval ((N : ℂ) ^ (-s)) * ev N hN0 s (Dp p) *
        (Z p.1 p.2 s * (QZ p.1 p.2).eval ((N : ℂ) ^ (-s)))) * ha +
      (c * Q.eval ((N : ℂ) ^ (-s)) * ev N hN0 s (Dp p) *
        ((N : ℂ) ^ ((mA p.1 p.2 : ℂ) * s) * (PA p.1 p.2).eval ((N : ℂ) ^ (-s)))) * hz

  have L2 : T md * mi Pd * DdL = C c * C cD * T kD * mi Qd * ∑ p : ι × κ,
      T (mAd p.1 p.2) * T (mZd p.1 p.2) * mi (PAd p.1 p.2) * mi (PZd p.1 p.2) * Ddp p := by
    refine eq_of_ev N hN0 hN _ _ σS fun s hs => ?_
    obtain ⟨⟨-, h3, -, h1⟩, hp⟩ := hS s hs
    simp only [map_mul, map_sum, ev_T, ev_C, ev_mi]
    rw [← hratd s h3, hsumd' s h1, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨-, hpA, -, hpZ⟩ := hp p
    have ha := hAdrat p.1 p.2 s hpA
    have hz := hZdrat p.1 p.2 s hpZ
    rw [hDdsplit p]
    simp only [map_mul, ev_mi]
    linear_combination (c * cD * (N : ℂ) ^ ((kD : ℂ) * s) * Qd.eval ((N : ℂ) ^ (-s)) * ev N hN0 s (Ddp p) *
        (Zd p.1 p.2 s * (QZd p.1 p.2).eval ((N : ℂ) ^ (-s)))) * ha +
      (c * cD * (N : ℂ) ^ ((kD : ℂ) * s) * Qd.eval ((N : ℂ) ^ (-s)) * ev N hN0 s (Ddp p) *
        ((N : ℂ) ^ ((mAd p.1 p.2 : ℂ) * s) * (PAd p.1 p.2).eval ((N : ℂ) ^ (-s)))) * hz

  have L1i : T (-m) * pl P * invert DL = C c * pl Q * ∑ p : ι × κ,
      T (-(mA p.1 p.2)) * T (-(mZ p.1 p.2)) * pl (PA p.1 p.2) * pl (PZ p.1 p.2) * invert (Dp p) := by
    have h := congrArg invert L1
    simpa only [map_mul, map_sum, invert_T, invert_C, invert_mi] using h

  have key : ∀ p : ι × κ,
      invert DL * (T (mAd p.1 p.2) * T (mZd p.1 p.2) * mi (PAd p.1 p.2) * mi (PZd p.1 p.2) * Ddp p) =
        C ΓA * C ΓZ * T kA * T kZ * DdL *
          (T (-(mA p.1 p.2)) * T (-(mZ p.1 p.2)) * pl (PA p.1 p.2) * pl (PZ p.1 p.2) * invert (Dp p)) := by
    intro p
    rw [hDsplit p, hDdsplit p, map_mul, map_mul, invert_mi, invert_mi]
    calc pl (QA p.1 p.2) * pl (QZ p.1 p.2) * invert (Dp p) *
          (T (mAd p.1 p.2) * T (mZd p.1 p.2) * mi (PAd p.1 p.2) * mi (PZd p.1 p.2) * Ddp p)
        = (T (mAd p.1 p.2) * mi (PAd p.1 p.2) * pl (QA p.1 p.2)) *
            (T (mZd p.1 p.2) * mi (PZd p.1 p.2) * pl (QZ p.1 p.2)) * invert (Dp p) * Ddp p := by ring
      _ = (C ΓA * T kA * T (-(mA p.1 p.2)) * pl (PA p.1 p.2) * mi (QAd p.1 p.2)) *
            (C ΓZ * T kZ * T (-(mZ p.1 p.2)) * pl (PZ p.1 p.2) * mi (QZd p.1 p.2)) * invert (Dp p) * Ddp p := by
          rw [FA p, FZ p]
      _ = C ΓA * C ΓZ * T kA * T kZ * (mi (QAd p.1 p.2) * mi (QZd p.1 p.2) * Ddp p) *
            (T (-(mA p.1 p.2)) * T (-(mZ p.1 p.2)) * pl (PA p.1 p.2) * pl (PZ p.1 p.2) * invert (Dp p)) := by ring
  have goalL : T md * mi Pd * pl Q =
      C cD * C ΓA * C ΓZ * (T kD * T kA * T kZ) * T (-m) * pl P * mi Qd := by
    have hE : invert DL * DdL ≠ 0 := mul_ne_zero (invert_ne_zero _ hDL0) hDdL0
    refine mul_left_cancel₀ hE ?_
    have eL : invert DL * DdL * (T md * mi Pd * pl Q) = ∑ p : ι × κ, pl Q * C c * C cD * T kD * mi Qd *
        (invert DL * (T (mAd p.1 p.2) * T (mZd p.1 p.2) * mi (PAd p.1 p.2) * mi (PZd p.1 p.2) * Ddp p)) := by
      rw [show invert DL * DdL * (T md * mi Pd * pl Q) = invert DL * pl Q * (T md * mi Pd * DdL) by ring, L2,
        Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    have eR : invert DL * DdL * (C cD * C ΓA * C ΓZ * (T kD * T kA * T kZ) * T (-m) * pl P * mi Qd) =
        ∑ p : ι × κ, pl Q * C c * C cD * T kD * mi Qd * (C ΓA * C ΓZ * T kA * T kZ * DdL *
          (T (-(mA p.1 p.2)) * T (-(mZ p.1 p.2)) * pl (PA p.1 p.2) * pl (PZ p.1 p.2) * invert (Dp p))) := by
      rw [show invert DL * DdL * (C cD * C ΓA * C ΓZ * (T kD * T kA * T kZ) * T (-m) * pl P * mi Qd) =
          DdL * C cD * C ΓA * C ΓZ * (T kD * T kA * T kZ) * mi Qd * (T (-m) * pl P * invert DL) by ring, L1i,
        Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [eL, eR]
    exact Finset.sum_congr rfl fun p _ => by rw [key p]

  intro s
  have h := congrArg (ev N hN0 s) goalL
  simp only [map_mul, ev_T, ev_C, ev_pl, ev_mi] at h
  rw [Polynomial.eval_one, Polynomial.eval_C, one_mul]
  have e1 : (N : ℂ) ^ (((kD + kA + kZ : ℤ) : ℂ) * s) =
      (N : ℂ) ^ ((kD : ℂ) * s) * (N : ℂ) ^ ((kA : ℂ) * s) * (N : ℂ) ^ ((kZ : ℂ) * s) := by
    push_cast
    rw [add_mul, add_mul, Complex.cpow_add _ _ hN0, Complex.cpow_add _ _ hN0]
  have e2 : (N : ℂ) ^ ((m : ℂ) * -s) = (N : ℂ) ^ (((-m : ℤ) : ℂ) * s) := by
    push_cast
    ring_nf
  rw [e1, e2]
  linear_combination h

end S_LanglandsTunnell_RankinSelberg_clearedFE_of_sum_mul_of_termwise_clearedFE
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_clearedFE_of_sum_mul_of_termwise_clearedFE (solution)
