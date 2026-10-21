-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_product_eq_Xprod
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T16:12:53.451801+00:00
-- url     : https://prove2.me/submissions/ca27ac2e-3227-4cf2-87ef-37503836ae07

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.Data.Fintype.Pi

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation OAI.PiExponent.LogarithmicJetIdeals

theorem solution {m : Nat} (c : Fin m -> Complex) (a : Complex)
    (d : Fin (m + 1) -> Nat) :
    OAI.PiExponent.LogarithmicJetIdeals.plainJet c
        (MvPolynomial.C a *
          Finset.prod Finset.univ (fun k : Fin (m + 1) =>
            (MvPolynomial.X k -
              MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k)) ^ d k)) =
      MvPowerSeries.C a *
        Finset.prod Finset.univ (fun k : Fin (m + 1) =>
          (MvPowerSeries.X k) ^ d k) := by
  classical
  rw [map_mul, map_prod]
  have hbase : ∀ k : Fin (m + 1),
      OAI.PiExponent.LogarithmicJetIdeals.plainJet c
        (MvPolynomial.X k - MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k)) =
        MvPowerSeries.X k := by
    intro k
    rw [map_sub]
    refine Fin.cases ?_ ?_ k
    · simp [OAI.PiExponent.LogarithmicJetIdeals.plainJet, MvPowerSeries.c_eq_algebraMap]
    · intro i
      simp only [OAI.PiExponent.LogarithmicJetIdeals.plainJet, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, Fin.cases_succ]
      rw [MvPowerSeries.c_eq_algebraMap]
      ring
  have hC : OAI.PiExponent.LogarithmicJetIdeals.plainJet c (MvPolynomial.C a) = MvPowerSeries.C a := by
    simp [OAI.PiExponent.LogarithmicJetIdeals.plainJet, MvPowerSeries.c_eq_algebraMap]
  simp only [map_pow]
  rw [hC]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [hbase]
