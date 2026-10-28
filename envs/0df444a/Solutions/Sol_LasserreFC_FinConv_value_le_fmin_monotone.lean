-- Prove2me | solution 1 for LasserreFC.FinConv.value_le_fmin_monotone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:05:15.454354+00:00
-- url     : https://prove2.me/submissions/ba5e6062-f103-4728-b38c-4ed86cd1cc28

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_Hierarchy

open MvPolynomial

namespace Aux_LasserreFC_FinConv_value_le_fmin_monotone

theorem eval_sumSq_nonneg {n : ℕ} (x : Fin n → ℝ) {p : MvPolynomial (Fin n) ℝ}
    (hp : IsSumSq p) : 0 ≤ eval x p := by
  induction hp with
  | zero => simp
  | sq_add a _ ih =>
    rw [eval_add, eval_mul]
    exact add_nonneg (mul_self_nonneg _) ih

end Aux_LasserreFC_FinConv_value_le_fmin_monotone

open LasserreFC.FinConv Aux_LasserreFC_FinConv_value_le_fmin_monotone in
theorem solution {n m1 m2 : ℕ} (P : POP n m1 m2) (fmin : ℝ)
    (hfmin : IsLeast ((fun x => eval x P.f) '' P.K) fmin) :
    (∀ k : ℕ, lasserreValue P k ≤ (fmin : EReal)) ∧ Monotone (lasserreValue P) := by
  constructor
  · intro k
    unfold lasserreValue
    apply sSup_le
    rintro _ ⟨γ, ⟨a, ⟨φ, rfl, -⟩, b, ⟨σ0, σ, hσ0, -, hσ, rfl⟩, hp⟩, rfl⟩
    rw [EReal.coe_le_coe_iff]
    obtain ⟨x, hxK, hx⟩ := hfmin.1
    have he := congrArg (eval x) hp
    simp only [eval_sub, eval_C, eval_add, map_sum, eval_mul] at he
    have hI : ∑ i, eval x (φ i) * eval x (P.h i) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hxK.1 i, mul_zero]
    have hQ : 0 ≤ ∑ j, eval x (σ j) * eval x (P.g j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (eval_sumSq_nonneg x (hσ j).1) (hxK.2 j)
    have h0 := eval_sumSq_nonneg x hσ0
    simp only at hx
    linarith
  · intro k k' hkk'
    unfold lasserreValue
    apply sSup_le_sSup
    apply Set.image_mono
    intro γ hγ
    obtain ⟨a, ⟨φ, ha, hφ⟩, b, ⟨σ0, σ, hσ0, hσ0d, hσ, hb⟩, hp⟩ := hγ
    exact ⟨a, ⟨φ, ha, fun i => (hφ i).trans (by omega)⟩, b,
      ⟨σ0, σ, hσ0, hσ0d.trans (by omega), fun j => ⟨(hσ j).1, (hσ j).2.trans (by omega)⟩, hb⟩, hp⟩
