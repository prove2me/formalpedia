-- Prove2me | solution 2 for OAI.PiExponent.exists_positive_separated_weights
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:24:52.253934+00:00
-- url     : https://prove2.me/submissions/b2327223-9c06-4c5d-960f-11e9183dd1bf

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Definitions.Def_PiExponent_DeterminantSetup
import Mathlib

section

open OAI.PiExponent.FormalInterpolation

namespace PiL16

lemma lift_pderiv (m : ℕ) (f : PowerSeries ℂ) (i : Fin m) :
    MvPowerSeries.pderiv ℂ i.succ (liftSeries m f) = 0 := by
  classical
  ext n
  rw [MvPowerSeries.coeff_pderiv, map_zero]
  set x := n + Finsupp.single i.succ 1
  have hx : x = Finsupp.cons (x 0) (Finsupp.tail x) := (Finsupp.cons_tail x).symm
  have htail : Finsupp.tail x ≠ 0 := by
    intro h
    have := congrArg (· i) h
    simp [x, Finsupp.tail_apply] at this
  rw [hx, ← MvPowerSeries.coeff_coeff_finSuccEquiv]
  simp only [liftSeries, RingHom.coe_comp, Function.comp_apply, AlgEquiv.toRingEquiv_eq_coe,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.apply_symm_apply,
    PowerSeries.coeff_map, MvPowerSeries.coeff_C, if_neg htail, zero_mul]

theorem gen_pderiv {m : Nat} (c : Fin m → Complex) (i : Fin m) : ∀ j : Fin (m + 1), MvPowerSeries.pderiv Complex i.succ (Fin.cases (1 + MvPowerSeries.X 0) (fun k => MvPowerSeries.C (c k) + MvPowerSeries.X k.succ + liftSeries m (PowerSeries.log Complex)) j) = if j = i.succ then 1 else 0 := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [Fin.cases_zero, map_add, MvPowerSeries.pderiv_one, zero_add]
    rw [MvPowerSeries.pderiv_X_of_ne (Fin.succ_ne_zero i).symm, if_neg (Fin.succ_ne_zero i).symm]
  · simp only [Fin.cases_succ, map_add, lift_pderiv, add_zero, MvPowerSeries.pderiv_C, zero_add]
    by_cases h : k = i
    · subst h; rw [MvPowerSeries.pderiv_X_self, if_pos rfl]
    · rw [MvPowerSeries.pderiv_X_of_ne (fun e => h (Fin.succ_injective _ e)),
        if_neg (fun e => h (Fin.succ_injective _ e))]

/-- greedy separated weights -/
def gW (S : List ℕ → ℕ) : ℕ → ℕ
  | n => S (List.ofFn (fun k : Fin n => gW S k)) + 1
decreasing_by exact k.isLt

theorem sep (m : ℕ) (S : List ℕ → ℕ) :
    ∃ w : Fin m → ℕ,
      (∀ i, 0 < w i) ∧ OAI.PiExponent.separatedWeights S w := by
  refine ⟨fun i => gW S i, fun i => by show 0 < gW S i; rw [gW]; omega, fun i => ?_⟩
  show _ ≤ gW S i
  conv_rhs => rw [gW]
  exact Nat.le_succ_of_le le_rfl

theorem sep2 (S : List ℕ → ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ w : Fin m → ℕ, (∀ i, 0 < w i) ∧ OAI.PiExponent.separatedWeights S w := sep m S

end PiL16

end

open OAI OAI.PiExponent


theorem solution
    (S : List ℕ → ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ w : Fin m → ℕ, (∀ i, 0 < w i) ∧ OAI.PiExponent.separatedWeights S w := by
  apply PiL16.sep2 <;> assumption
