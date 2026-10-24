-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.formalJet_logarithmicFrameDerivative_zero_coeff_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:24:08.14498+00:00
-- url     : https://prove2.me/submissions/a4445381-65ea-48a8-bbab-43a89a8741c7

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv

section

open OAI.PiExponent.FormalInterpolation

namespace PiL17

theorem chain_full {σ R S : Type*} [Fintype σ] [CommSemiring R] [CommSemiring S] [Algebra R S]
    [DecidableEq σ] (D : Derivation R S S) (g : σ → S) (p : MvPolynomial σ R) :
    D (MvPolynomial.aeval g p) = ∑ k, MvPolynomial.aeval g (MvPolynomial.pderiv k p) * D (g k) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have e1 : ∀ k, MvPolynomial.pderiv k (p * MvPolynomial.X j) =
        p * MvPolynomial.pderiv k (MvPolynomial.X j) + MvPolynomial.X j * MvPolynomial.pderiv k p := by
      intro k; rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have e2 : D (MvPolynomial.aeval g p * g j) =
        MvPolynomial.aeval g p * D (g j) + g j * D (MvPolynomial.aeval g p) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [map_mul, MvPolynomial.aeval_X, e2, hp]
    simp_rw [e1, map_add, map_mul, MvPolynomial.aeval_X, add_mul, Finset.sum_add_distrib]
    congr 1
    · simp [MvPolynomial.pderiv_X, Pi.single_apply]
    · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

lemma coeff_lift (m : ℕ) (f : PowerSeries ℂ) (x : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff x (liftSeries m f) =
      if Finsupp.tail x = 0 then PowerSeries.coeff (x 0) f else 0 := by
  classical
  conv_lhs => rw [← Finsupp.cons_tail x]
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv]
  simp only [liftSeries, RingHom.coe_comp, Function.comp_apply, AlgEquiv.toRingEquiv_eq_coe,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.apply_symm_apply,
    PowerSeries.coeff_map, MvPowerSeries.coeff_C]

lemma lift_pderiv0 (m : ℕ) (f : PowerSeries ℂ) :
    MvPowerSeries.pderiv ℂ 0 (liftSeries m f) = liftSeries m (PowerSeries.derivative ℂ f) := by
  classical
  ext n
  rw [MvPowerSeries.coeff_pderiv, coeff_lift, coeff_lift]
  have ht : Finsupp.tail (n + Finsupp.single 0 1) = Finsupp.tail n := by
    ext i; simp [Finsupp.tail_apply]
  rw [ht]
  split_ifs
  · rw [PowerSeries.coeff_derivative]; simp
  · simp

lemma lift_X (m : ℕ) : liftSeries m PowerSeries.X = MvPowerSeries.X 0 := by
  simp only [liftSeries, RingHom.coe_comp, Function.comp_apply, PowerSeries.map_X]
  exact (MvPowerSeries.finSuccEquiv ℂ m).symm_apply_eq.2 (MvPowerSeries.finSuccEquiv_X_zero).symm

lemma log_deriv : (1 + PowerSeries.X) * PowerSeries.derivative ℂ (PowerSeries.log ℂ) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [pow_succ]

lemma key (m : ℕ) : (1 + MvPowerSeries.X 0) * MvPowerSeries.pderiv ℂ 0 (liftSeries m (PowerSeries.log ℂ)) = 1 := by
  rw [lift_pderiv0, ← lift_X, ← map_one (liftSeries m), ← map_add, ← map_mul, log_deriv, map_one]

theorem zero_coeff {m : Nat} (c : Fin m → Complex) (F : MvPolynomial (Fin (m + 1)) Complex) (a : Fin (m + 1) →₀ Nat) : MvPowerSeries.coeff a (formalJet c (logarithmicFrameDerivative 0 F)) = (a 0 : Complex) * MvPowerSeries.coeff a (formalJet c F) + ((a 0 : Complex) + 1) * MvPowerSeries.coeff (a + Finsupp.single 0 1) (formalJet c F) := by
  classical
  set g : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ := Fin.cases (1 + MvPowerSeries.X 0)
    (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + liftSeries m (PowerSeries.log ℂ)) with hg
  have hjet : ∀ P, formalJet c P = MvPolynomial.aeval g P := fun P => rfl
  let D : Derivation ℂ (MvPowerSeries (Fin (m + 1)) ℂ) (MvPowerSeries (Fin (m + 1)) ℂ) :=
    MvPowerSeries.pderiv ℂ 0
  have hD0 : D (g 0) = 1 := by
    simp [D, g, MvPowerSeries.pderiv_X_self]
  have hDs : ∀ i : Fin m, D (g i.succ) = D (liftSeries m (PowerSeries.log ℂ)) := by
    intro i
    simp [D, g, MvPowerSeries.pderiv_X_of_ne (Fin.succ_ne_zero i)]
  have hmain : formalJet c (logarithmicFrameDerivative 0 F) =
      (1 + MvPowerSeries.X 0) * D (formalJet c F) := by
    rw [hjet, hjet, chain_full, Fin.sum_univ_succ, hD0]
    simp_rw [hDs]
    simp only [logarithmicFrameDerivative, Fin.cases_zero, map_add, map_mul, map_sum,
      MvPolynomial.aeval_X]
    rw [mul_add, Finset.mul_sum, mul_one]
    have hg0 : g 0 = 1 + MvPowerSeries.X 0 := rfl
    rw [hg0]
    have hk : (1 + MvPowerSeries.X 0) * D (liftSeries m (PowerSeries.log ℂ)) = 1 := key m
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (-(MvPolynomial.aeval g (MvPolynomial.pderiv i.succ F))) * hk
  rw [hmain, add_mul, one_mul, map_add, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul,
    MvPowerSeries.coeff_pderiv]
  by_cases ha : a 0 = 0
  · have : ¬ Finsupp.single (0 : Fin (m + 1)) 1 ≤ a := by
      intro h; have := h 0; simp at this; omega
    rw [if_neg this, ha]; simp
  · have hle : Finsupp.single (0 : Fin (m + 1)) 1 ≤ a := by
      intro i
      by_cases hi : i = 0
      · subst hi; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hi]
    rw [if_pos hle, MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle]
    have : ((a - Finsupp.single 0 1 : Fin (m + 1) →₀ ℕ) 0 : ℕ) + 1 = a 0 := by simp; omega
    have hc : (((a - Finsupp.single 0 1 : Fin (m + 1) →₀ ℕ) 0 : ℕ) : ℂ) + 1 = (a 0 : ℂ) := by exact_mod_cast this
    rw [hc]; ring

end PiL17

end

open OAI OAI.PiExponent OAI.PiExponent.FormalInterpolation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution {m : Nat} (c : Fin m → Complex) (F : MvPolynomial (Fin (m + 1)) Complex) (a : Fin (m + 1) →₀ Nat) : MvPowerSeries.coeff a (formalJet c (logarithmicFrameDerivative 0 F)) = (a 0 : Complex) * MvPowerSeries.coeff a (formalJet c F) + ((a 0 : Complex) + 1) * MvPowerSeries.coeff (a + Finsupp.single 0 1) (formalJet c F) := by
  apply PiL17.zero_coeff <;> assumption
