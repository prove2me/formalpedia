-- Prove2me | solution 1 for Kyprianou.Ch04.negativeExponentIntegerDivergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:25:15.838199+00:00
-- url     : https://prove2.me/submissions/6698b605-2598-46f8-a41f-7b3bf7c68aa3

import Theorems.Thm_Kyprianou_Ch04_negativeExponentIntegerTailBound
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (theta : Real) (htheta : 0 < theta) (hpsi : L.ψ theta < 0) :
    ∀ᵐ omega ∂P, Tendsto (fun n : Nat => L.X (n : NNReal) omega) atTop atBot := by
  let a : Real := L.ψ theta / 2
  let r : ENNReal := ENNReal.ofReal (Real.exp a)
  have ha : a < 0 := by dsimp [a]; linarith
  have hr : r < 1 := by
    have hh := (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (Real.exp_lt_one_iff.2 ha)
    simpa [r] using hh
  let E : Nat → Set Omega := fun n =>
    {w | (n : Real) * a ≤ theta * L.X (n : NNReal) w}
  have hE (n : Nat) : P (E n) ≤ r ^ n :=
    Kyprianou.Ch04.negativeExponentIntegerTailBound P F L theta htheta.le n
  have hsum : (∑' n, P (E n)) ≠ ⊤ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' n : Nat, r ^ n := ENNReal.tsum_le_tsum hE
      _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        exact ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hr)
  filter_upwards [ae_eventually_notMem hsum] with w hw
  apply tendsto_atBot.2
  intro b
  obtain ⟨K, hK⟩ := exists_nat_gt (-(theta * b) / (-a))
  filter_upwards [hw, eventually_ge_atTop K] with n hn hnK
  change ¬ (n : Real) * a ≤ theta * L.X (n : NNReal) w at hn
  have hk : -(theta * b) < (K : Real) * (-a) :=
    (div_lt_iff₀ (neg_pos.mpr ha)).1 hK
  have hkn : (K : Real) ≤ (n : Real) := by exact_mod_cast hnK
  have hmul := mul_le_mul_of_nonneg_right hkn (neg_nonneg.mpr ha.le)
  have hb : theta * L.X (n : NNReal) w < theta * b := by linarith
  exact (lt_of_mul_lt_mul_left hb htheta.le).le
