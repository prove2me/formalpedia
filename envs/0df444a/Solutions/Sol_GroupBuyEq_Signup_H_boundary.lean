-- Prove2me | solution 1 for GroupBuyEq.Signup.H_boundary
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:47:27.559349+00:00
-- url     : https://prove2.me/submissions/5fd6cad9-e710-4c0b-9d5e-997d8d2343f8

import Mathlib
import Definitions.Def_GroupBuyEq_Signup_Model

open MeasureTheory Set in
open GroupBuyEq.Signup in
theorem solution (P : Params) (hP : P.Standing) (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ] (E : Profile)
    (hE : IsEquilibrium P μ E) (k : ℕ) (hk : P.M2 ≤ k + 1) (t : ℝ) (ht : t ∈ Set.Icc 0 P.T) :
    H P μ E k t = 1 - ProbabilityTheory.cdf μ P.p2 := by
  obtain ⟨h1, h2⟩ := hE.2.2.1 (k + 1) hk t ht
  have hd : 0 < P.d := hP.2.2.2.2.1
  have hset : {u | 0 ≤ V P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t) u} = Ici P.p2 := by
    ext u
    simp only [mem_setOf_eq, mem_Ici, h1, h2, V, zero_mul, one_mul, zero_add, sub_zero,
      sub_self, add_zero]
    rw [le_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h; left; linarith
  unfold H
  rw [hset, ← measure_congr (Ioi_ae_eq_Ici (μ := μ) (a := P.p2)), ← compl_Iic,
    ProbabilityTheory.cdf_eq_real]
  exact probReal_compl_eq_one_sub measurableSet_Iic
