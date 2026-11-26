-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RecoveryRecordPrefixV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:31:21.941127+00:00
-- url     : https://prove2.me/submissions/d3628d9e-6881-4a96-891a-b58738e5982a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (w : Omega) (a : NNReal)
    (hBound : ∀ t : NNReal, L.X t w ≤ (t : Real)) :
    let R : WithTop NNReal := ⨅ t : NNReal, if (a : WithTop NNReal) < (t : WithTop NNReal) ∧
      (a : Real) < L.X t w then (t : WithTop NNReal) else ⊤
    (a : WithTop NNReal) ≤ R ∧
      (∀ t : NNReal, (t : WithTop NNReal) < R → L.X t w ≤ (a : Real)) ∧
      (R ≠ ⊤ → L.X (R.untopD 0) w = (a : Real)) := by
  classical
  dsimp only
  let R : WithTop NNReal := ⨅ t : NNReal, if (a : WithTop NNReal) < (t : WithTop NNReal) ∧
    (a : Real) < L.X t w then (t : WithTop NNReal) else ⊤
  have hGate (t : NNReal) : (a : Real) < L.X t w →
      (a : WithTop NNReal) < (t : WithTop NNReal) := by
    intro h
    exact WithTop.coe_lt_coe.mpr (by exact_mod_cast h.trans_le (hBound t))
  have hLower : (a : WithTop NNReal) ≤ R := by
    apply le_iInf
    intro t
    split
    · rename_i h
      exact h.1.le
    · exact le_top
  have hpre (t : NNReal) (ht : (t : WithTop NNReal) < R) : L.X t w ≤ (a : Real) := by
    by_contra hn
    have h : (a : Real) < L.X t w := lt_of_not_ge hn
    have hh : R ≤ (t : WithTop NNReal) :=
      iInf_le_of_le t (by rw [if_pos ⟨hGate t h,h⟩])
    exact (not_lt_of_ge hh) ht
  refine ⟨hLower,hpre,?_⟩
  intro hf
  let r : NNReal := R.untopD 0
  have hr : (r : WithTop NNReal) = R :=
    WithTop.coe_untop₀_of_ne_top (show R ≠ ⊤ from hf)
  have he : R = ⨅ (t : NNReal) (_ : (a : Real) < L.X t w), (t : WithTop NNReal) := by
    apply le_antisymm
    · apply le_iInf
      intro t
      apply le_iInf
      intro ht
      exact iInf_le_of_le t (by rw [if_pos ⟨hGate t ht,ht⟩])
    · apply le_iInf
      intro t
      split
      · rename_i ht
        exact iInf_le_of_le t (iInf_le _ ht.2)
      · exact le_top
  exact firstUpcrossing_value_eq_threshold L (a : Real) a.coe_nonneg w r (hr.trans he)
