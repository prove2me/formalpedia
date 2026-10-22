-- Prove2me | solution 1 for MultistageRUC.WitPolicy.ramp_worst_case_in_four
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:01:14.187767+00:00
-- url     : https://prove2.me/submissions/376988fd-6d4a-418a-bd39-6e64950f84be

import Mathlib
import Definitions.Def_MultistageRUC_WitPolicy_Setting

set_option autoImplicit false
open MultistageRUC.WitPolicy

theorem solution {Ng Nd T : ℕ}
    (W : Fin Ng → Fin T → ℝ) (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ)
    (dmax dmin : Fin T → Fin Nd → ℝ)
    (hmax : IsMaxLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmax)
    (hmin : IsMinLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmin)
    (i : Fin Ng) (s t : Fin T) (hst : t.val = s.val + 1) :
    ∀ d ∈ MultistageRUC.Equiv.uncSet dbar dhat Γ,
      (∃ d' ∈ ({dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} :
          Set (Fin T → Fin Nd → ℝ)),
        W i t * totalLoad d t - W i s * totalLoad d s ≤
          W i t * totalLoad d' t - W i s * totalLoad d' s) ∧
      (∃ d' ∈ ({dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} :
          Set (Fin T → Fin Nd → ℝ)),
        W i t * totalLoad d' t - W i s * totalLoad d' s ≤
          W i t * totalLoad d t - W i s * totalLoad d s) := by
  intro d hd
  have hst' : s < t := by
    rw [Fin.lt_def]; omega
  have ht1 := hmax.2 d hd t
  have ht2 := hmin.2 d hd t
  have hs1 := hmax.2 d hd s
  have hs2 := hmin.2 d hd s
  have e1 : totalLoad (dminmax dmin dmax t) t = totalLoad dmax t := by
    simp [totalLoad, dminmax]
  have e2 : totalLoad (dminmax dmin dmax t) s = totalLoad dmin s := by
    simp [totalLoad, dminmax, hst']
  have e3 : totalLoad (dmaxmin dmin dmax t) t = totalLoad dmin t := by
    simp [totalLoad, dmaxmin]
  have e4 : totalLoad (dmaxmin dmin dmax t) s = totalLoad dmax s := by
    simp [totalLoad, dmaxmin, hst']
  constructor
  · rcases le_total 0 (W i t) with hA | hA <;> rcases le_total 0 (W i s) with hB | hB
    · -- coefficient of L_t ≥ 0, of L_s ≤ 0: want max L_t, min L_s
      refine ⟨dminmax dmin dmax t, by simp, ?_⟩
      rw [e1, e2]; nlinarith [mul_le_mul_of_nonneg_left ht1 hA, mul_le_mul_of_nonneg_left hs2 hB]
    · refine ⟨dmax, by simp, ?_⟩
      nlinarith [mul_le_mul_of_nonneg_left ht1 hA, mul_le_mul_of_nonpos_left hs1 hB]
    · refine ⟨dmin, by simp, ?_⟩
      nlinarith [mul_le_mul_of_nonpos_left ht2 hA, mul_le_mul_of_nonneg_left hs2 hB]
    · refine ⟨dmaxmin dmin dmax t, by simp, ?_⟩
      rw [e3, e4]; nlinarith [mul_le_mul_of_nonpos_left ht2 hA, mul_le_mul_of_nonpos_left hs1 hB]
  · rcases le_total 0 (W i t) with hA | hA <;> rcases le_total 0 (W i s) with hB | hB
    · refine ⟨dmaxmin dmin dmax t, by simp, ?_⟩
      rw [e3, e4]; nlinarith [mul_le_mul_of_nonneg_left ht2 hA, mul_le_mul_of_nonneg_left hs1 hB]
    · refine ⟨dmin, by simp, ?_⟩
      nlinarith [mul_le_mul_of_nonneg_left ht2 hA, mul_le_mul_of_nonpos_left hs2 hB]
    · refine ⟨dmax, by simp, ?_⟩
      nlinarith [mul_le_mul_of_nonpos_left ht1 hA, mul_le_mul_of_nonneg_left hs1 hB]
    · refine ⟨dminmax dmin dmax t, by simp, ?_⟩
      rw [e1, e2]; nlinarith [mul_le_mul_of_nonpos_left ht1 hA, mul_le_mul_of_nonpos_left hs2 hB]
