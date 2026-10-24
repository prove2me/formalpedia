-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.formalJet_logarithmicFrameDerivative_zero_series_chain_rule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:06:24.643986+00:00
-- url     : https://prove2.me/submissions/0d1b5cf4-e27f-4a22-a61d-4a4c51d39442

import Mathlib
import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace PXCR

lemma coeff_lift (m : ℕ) (f : PowerSeries ℂ) (k : ℕ) (x : Fin m →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.cons k x) (liftSeries m f) =
      if x = 0 then PowerSeries.coeff k f else 0 := by
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv]
  simp only [liftSeries, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.apply_symm_apply,
    PowerSeries.coeff_map, MvPowerSeries.coeff_C]

lemma coeff_lift' (m : ℕ) (f : PowerSeries ℂ) (a : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff a (liftSeries m f) =
      if Finsupp.tail a = 0 then PowerSeries.coeff (a 0) f else 0 := by
  conv_lhs => rw [← Finsupp.cons_tail a]
  exact coeff_lift m f (a 0) (Finsupp.tail a)

lemma pderiv_lift (m : ℕ) (f : PowerSeries ℂ) :
    MvPowerSeries.pderiv ℂ (0 : Fin (m + 1)) (liftSeries m f) =
      liftSeries m (PowerSeries.derivative ℂ f) := by
  ext a
  rw [MvPowerSeries.coeff_pderiv, coeff_lift', coeff_lift', PowerSeries.coeff_derivative]
  have ht : Finsupp.tail (a + Finsupp.single 0 1) = Finsupp.tail a := by
    ext j; simp [Finsupp.tail_apply, Finsupp.single_apply, Fin.succ_ne_zero]
  have h0 : ((a + Finsupp.single (0 : Fin (m + 1)) 1 : Fin (m + 1) →₀ ℕ) 0) = a 0 + 1 := by simp
  rw [ht, h0]
  split_ifs <;> push_cast <;> ring

lemma lift_X (m : ℕ) : liftSeries m PowerSeries.X = MvPowerSeries.X 0 := by
  simp only [liftSeries, RingHom.coe_comp, Function.comp_apply, PowerSeries.map_X,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_eq, MvPowerSeries.finSuccEquiv_X_zero]

lemma one_add_mul_dlog :
    (1 + PowerSeries.X) * PowerSeries.derivative ℂ (PowerSeries.log ℂ) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [PowerSeries.coeff_one, pow_succ]

lemma key (m : ℕ) :
    (1 + MvPowerSeries.X (0 : Fin (m + 1))) *
      MvPowerSeries.pderiv ℂ (0 : Fin (m + 1)) (liftSeries m (PowerSeries.log ℂ)) = 1 := by
  rw [pderiv_lift, ← lift_X, ← map_one (liftSeries m), ← map_add, ← map_mul, one_add_mul_dlog, map_one]

lemma lfd_eq {m : ℕ} (F : MvPolynomial (Fin (m + 1)) ℂ) :
    logarithmicFrameDerivative 0 F =
      MvPolynomial.X 0 * MvPolynomial.pderiv 0 F + ∑ j : Fin m, MvPolynomial.pderiv j.succ F := rfl

lemma lfd_add {m : ℕ} (F G : MvPolynomial (Fin (m + 1)) ℂ) :
    logarithmicFrameDerivative 0 (F + G) =
      logarithmicFrameDerivative 0 F + logarithmicFrameDerivative 0 G := by
  simp only [lfd_eq, map_add, mul_add, Finset.sum_add_distrib]; ring

lemma lfd_mul {m : ℕ} (F G : MvPolynomial (Fin (m + 1)) ℂ) :
    logarithmicFrameDerivative 0 (F * G) =
      logarithmicFrameDerivative 0 F * G + F * logarithmicFrameDerivative 0 G := by
  simp only [lfd_eq, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum, add_mul, mul_add]
  ring

lemma gen {m : ℕ} (c : Fin m → ℂ) (k : Fin (m + 1)) :
    formalJet c (logarithmicFrameDerivative 0 (MvPolynomial.X k)) =
      (1 + MvPowerSeries.X (0 : Fin (m + 1))) *
        MvPowerSeries.pderiv ℂ (0 : Fin (m + 1)) (formalJet c (MvPolynomial.X k)) := by
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [lfd_eq]
    simp [formalJet, MvPolynomial.pderiv_X, Pi.single_apply, Fin.succ_ne_zero]
  · rw [lfd_eq]
    simp only [formalJet, MvPolynomial.aeval_X, Fin.cases_succ, map_add]
    have h1 : MvPolynomial.pderiv (0 : Fin (m + 1)) (MvPolynomial.X j.succ : MvPolynomial (Fin (m + 1)) ℂ) = 0 := by
      rw [MvPolynomial.pderiv_X]; simp [Pi.single_apply, (Fin.succ_ne_zero j)]
    have h2 : ∑ x : Fin m, MvPolynomial.pderiv x.succ (MvPolynomial.X j.succ : MvPolynomial (Fin (m + 1)) ℂ) = 1 := by
      simp [MvPolynomial.pderiv_X, Pi.single_apply, Fin.succ_inj]
    rw [h1, h2, mul_zero, map_zero, zero_add, map_one]
    have h3 : MvPowerSeries.pderiv ℂ (0 : Fin (m + 1)) (MvPowerSeries.C (c j)) = 0 := MvPowerSeries.pderiv_C
    have h4 : MvPowerSeries.pderiv ℂ (0 : Fin (m + 1)) (MvPowerSeries.X j.succ : MvPowerSeries (Fin (m + 1)) ℂ) = 0 :=
      MvPowerSeries.pderiv_X_of_ne (Fin.succ_ne_zero j)
    rw [h3, h4, zero_add, zero_add, key]

theorem chain {m : ℕ} (c : Fin m → ℂ) (F : MvPolynomial (Fin (m + 1)) ℂ) :
    formalJet c (logarithmicFrameDerivative (0 : Fin (m + 1)) F) =
      ((1 : MvPowerSeries (Fin (m + 1)) Complex) + MvPowerSeries.X (0 : Fin (m + 1))) *
        MvPowerSeries.pderiv Complex (0 : Fin (m + 1)) (formalJet c F) := by
  induction F using MvPolynomial.induction_on with
  | C z =>
    have : logarithmicFrameDerivative (0 : Fin (m + 1)) (MvPolynomial.C z : MvPolynomial (Fin (m + 1)) ℂ) = 0 := by
      simp [lfd_eq]
    rw [this, map_zero, MvPolynomial.algHom_C, Derivation.map_algebraMap, mul_zero]
  | add p q hp hq => rw [lfd_add, map_add, hp, hq, map_add, map_add, mul_add]
  | mul_X p k hp =>
    rw [lfd_mul, map_add, map_mul, map_mul, hp, gen, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring

end PXCR

theorem solution {m : Nat} (c : Fin m → Complex) (F : MvPolynomial (Fin (m + 1)) Complex) :
    formalJet c (logarithmicFrameDerivative (0 : Fin (m + 1)) F) =
      ((1 : MvPowerSeries (Fin (m + 1)) Complex) + MvPowerSeries.X (0 : Fin (m + 1))) *
        MvPowerSeries.pderiv Complex (0 : Fin (m + 1)) (formalJet c F) :=
  PXCR.chain c F
