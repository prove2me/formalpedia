-- Prove2me | solution 1 for MoneyBurningSurplus.Harmonic.vcg_utility_eq
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T16:06:20.997724+00:00
-- url     : https://prove2.me/submissions/b0f7d5cf-6c65-425a-8d61-8bf0fd6cfb2e

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model
set_option autoImplicit false
open MoneyBurningSurplus.Harmonic

theorem solution
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (tb : Finset O → O) (htb : IsTieBreak tb)
    (v : Fin n → O → ℝ) (hv : AGT.IsValProfile valuationDomain v)
    (R : Finset (Fin n)) (i : Fin n) (hi : i ∈ R) :
    v i (vcgOutcome tb R v) - hasmPay tb R i v =
      welfare v R - welfare v (R.erase i) := by
  classical
  have hne : (maximizers v R).Nonempty := by
    obtain ⟨o, ho, hmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset O).Nonempty)
      (fun o => ∑ i ∈ R, v i o)
    refine ⟨o, ?_⟩
    simp only [maximizers, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmax.symm
  have hmem := htb (maximizers v R) hne
  have hmax : (∑ j ∈ R, v j (vcgOutcome tb R v)) = welfare v R := by
    simpa [vcgOutcome, maximizers] using hmem
  have hsum := Finset.add_sum_erase R (fun j => v j (vcgOutcome tb R v)) hi
  simp only [hasmPay, hi, ↓reduceIte]
  linarith
#print axioms solution
