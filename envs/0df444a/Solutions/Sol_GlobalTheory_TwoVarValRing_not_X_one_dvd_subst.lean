-- Prove2me | solution 1 for GlobalTheory.TwoVarValRing.not_X_one_dvd_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:58:00.340621+00:00
-- url     : https://prove2.me/submissions/2d1b4a6c-b243-477b-b10c-2c35081d3643

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalRingSecondVariable
import Theorems.Thm_GlobalTheory_TwoVarValRing_not_X_one_dvd_X_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TwoVarValRing
namespace GlobalTheory.TwoVarValRing
theorem _root_.solution (k : Type) [Field k] (b : PowerSeries k) (hb : b ≠ 0) :
    ¬ MvPowerSeries.X 1 ∣ b.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.X 0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb
    (PowerSeries.X_prime (R := k)).irreducible
  rw [PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs]
  apply not_X_dvd_mul
  · intro h
    have hu : IsUnit ((u : PowerSeries k).subst
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)) := by
      rw [← PowerSeries.coe_substAlgHom hs]
      exact u.isUnit.map _
    exact not_X_dvd_one (R := k) (1 : Fin 2) (h.trans hu.dvd)
  · induction n with
    | zero => simpa using not_X_dvd_one (R := k) (1 : Fin 2)
    | succ n ih =>
      rw [pow_succ]
      exact not_X_dvd_mul _ (ih (by simp)) (not_X_one_dvd_X_zero k)
end GlobalTheory.TwoVarValRing
