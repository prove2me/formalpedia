-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_logarithmic_jet_gluing_varying_sets
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-12T18:46:32.990326+00:00
-- url     : https://prove2.me/submissions/7e8402fa-8a99-4781-8c8b-6627b1964b74

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPowerSeries.Order

open OAI.PiExponent
open scoped BigOperators

noncomputable section

private def orderIdeal {σ : Type*} (n : ℕ) : Ideal (MvPowerSeries σ ℂ) where
  carrier := {f | (n : ℕ∞) ≤ f.order}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact (le_min hf hg).trans MvPowerSeries.min_order_le_add
  smul_mem' := by
    intro r f hf
    change (n : ℕ∞) ≤ (r * f).order
    exact hf.trans ((le_add_left le_rfl).trans MvPowerSeries.le_order_mul)

private theorem order_of_mem_ker_pow {R σ : Type*} [CommRing R]
    (F : R →+* MvPowerSeries σ ℂ) (n : ℕ) {p : R}
    (hp : p ∈ (RingHom.ker (MvPowerSeries.constantCoeff.comp F)) ^ n) :
    (n : ℕ∞) ≤ (F p).order := by
  have h : (RingHom.ker (MvPowerSeries.constantCoeff.comp F)) ^ n ≤
      (orderIdeal n).comap F := by
    clear hp
    induction n with
    | zero =>
        intro p hp
        change (0 : ℕ∞) ≤ (F p).order
        exact bot_le
    | succ n ih =>
        rw [pow_succ]
        apply Ideal.mul_le.mpr
        intro r hr s hs
        have hr' := ih hr
        have hs' : (1 : ℕ∞) ≤ (F s).order :=
          MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hs
        change (n : ℕ∞) ≤ (F r).order at hr'
        change ((n + 1 : ℕ) : ℕ∞) ≤ (F (r * s)).order
        rw [map_mul, Nat.cast_add, Nat.cast_one]
        exact (add_le_add hr' hs').trans MvPowerSeries.le_order_mul
  exact h hp

private def centerEval {m : ℕ} (c : Fin m → ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ →+* ℂ :=
  MvPowerSeries.constantCoeff.comp (FormalInterpolation.formalJet c).toRingHom

private theorem centerEval_C {m : ℕ} (c : Fin m → ℂ) (z : ℂ) :
    centerEval c (MvPolynomial.C z) = z := by
  simp [centerEval, FormalInterpolation.formalJet, MvPowerSeries.algebraMap_apply]

private theorem centerEval_X_sub {m : ℕ} (c d : Fin m → ℂ) (i : Fin m) :
    centerEval c (MvPolynomial.X i.succ) - centerEval d (MvPolynomial.X i.succ) =
      c i - d i := by
  simp [centerEval, FormalInterpolation.formalJet, MvPolynomial.aeval_X]

private theorem center_ideals_coprime {m : ℕ} (c d : Fin m → ℂ) (hcd : c ≠ d) :
    IsCoprime (RingHom.ker (centerEval c)) (RingHom.ker (centerEval d)) := by
  have hmax (e : Fin m → ℂ) : (RingHom.ker (centerEval e)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (centerEval e)
      (fun z => ⟨MvPolynomial.C z, centerEval_C e z⟩)
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply (hmax c).coprime_of_ne (hmax d)
  intro h
  apply hcd
  funext i
  let x : MvPolynomial (Fin (m + 1)) ℂ := MvPolynomial.X i.succ
  have hx : x - MvPolynomial.C (centerEval c x) ∈ RingHom.ker (centerEval c) := by
    simp [RingHom.mem_ker, map_sub, centerEval_C]
  rw [h] at hx
  have hx' : centerEval d x = centerEval c x := by
    simpa [RingHom.mem_ker, map_sub, centerEval_C, sub_eq_zero] using hx
  have hd := centerEval_X_sub c d i
  change centerEval c x - centerEval d x = c i - d i at hd
  rw [hx', sub_self] at hd
  exact sub_eq_zero.mp hd.symm

/-- Finite logarithmic jets at distinct centers can be glued, with independently chosen indices. -/
theorem solution
    {m : ℕ} {J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (S : J → Finset (Fin (m + 1) → ℕ))
    (Q : J → MvPolynomial (Fin (m + 1)) ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ j : J, ∀ a : {a // a ∈ S j},
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet (c j) P) =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet (c j) (Q j)) := by
  classical
  let N : J → ℕ := fun j =>
    (S j).sup (fun a => Finsupp.degree (InterpolationMatrix.exponentVector a)) + 1
  let I : J → Ideal (MvPolynomial (Fin (m + 1)) ℂ) :=
    fun j => (RingHom.ker (centerEval (c j))) ^ N j
  have hI : Pairwise (fun j k => IsCoprime (I j) (I k)) := by
    intro j k hjk
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact Ideal.pow_sup_pow_eq_top
      (center_ideals_coprime (c j) (c k) (fun h => hjk (hc h))).sup_eq
  obtain ⟨P, hP⟩ := Ideal.exists_forall_sub_mem_ideal hI Q
  refine ⟨P, ?_⟩
  intro j a
  have horder : (N j : ℕ∞) ≤
      (FormalInterpolation.formalJet (c j) (P - Q j)).order :=
    order_of_mem_ker_pow (FormalInterpolation.formalJet (c j)).toRingHom (N j) (hP j)
  have hdegree : Finsupp.degree (InterpolationMatrix.exponentVector a.val) < N j :=
    Nat.lt_succ_of_le (Finset.le_sup
      (f := fun b => Finsupp.degree (InterpolationMatrix.exponentVector b)) a.property)
  have hz := MvPowerSeries.coeff_of_lt_order
    ((Nat.cast_lt.mpr hdegree).trans_le horder)
  simpa only [map_sub, sub_eq_zero] using hz
