-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:13:31.275388+00:00
-- url     : https://prove2.me/submissions/3d6dd116-6fa5-46b2-85f1-9caf2a67dac1

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Mathlib.RingTheory.MvPowerSeries.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

theorem solution
    {m : ℕ} (b : Fin m → ℕ)
    (f : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hf : ∀ i : Fin m, ∀ d : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff d (f i) ≠ 0 → d i.succ ≤ b i)
    (hzero : ∀ i : Fin m, ∀ d : Fin (m + 1) →₀ ℕ, ∀ j : Fin m,
      j ≠ i → d j.succ ≠ 0 → MvPowerSeries.coeff d (f i) = 0)
    (e : Fin (m + 1) →₀ ℕ)
    (hne : MvPowerSeries.coeff e (∏ i : Fin m, f i) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ b i := by
  classical
  have hcoeff := MvPowerSeries.coeff_prod f e Finset.univ
  rw [hcoeff] at hne
  obtain ⟨l, hlmem, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hsum := (Finset.mem_finsuppAntidiag.mp hlmem).1
  have hterm_i (j : Fin m) : MvPowerSeries.coeff (l j) (f j) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hterm) j (Finset.mem_univ j)
  intro i
  have hcoordzero (j : Fin m) (hji : j ≠ i) : l j i.succ = 0 := by
    by_contra h
    have hcoeffzero := hzero j (l j) i (Ne.symm hji) h
    exact hterm_i j hcoeffzero
  have heval : e i.succ = ∑ j ∈ (Finset.univ : Finset (Fin m)), l j i.succ := by
    simpa using (congrArg (fun d : (Fin (m + 1) →₀ ℕ) => d i.succ) hsum).symm
  have hsumcoord :
      (∑ j ∈ (Finset.univ : Finset (Fin m)), l j i.succ) = l i i.succ := by
    rw [Finset.sum_eq_single i]
    · intro j hjmem hjne
      exact hcoordzero j hjne
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  calc
    e i.succ = l i i.succ := heval.trans hsumcoord
    _ ≤ b i := hf i (l i) (hterm_i i)
