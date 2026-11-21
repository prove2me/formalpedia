-- Prove2me | solution 1 for MasulloRH.regularized_initial_identity_iff_scalar_bound
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:32:50.512769+00:00
-- url     : https://prove2.me/submissions/75b8ac10-8599-4f46-bd65-f9c89dd8f71d

import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_single_resolvent_test

open MasulloRH

theorem solution (α : ℝ) :
    (∀ s : ℂ, (3 / 2 : ℝ) < s.re → regularizedTraceRHS α s = zetaLogDeriv s) ↔
    (zetaLogDeriv 3).re ≤ (regularizedTraceRHS α 3).re := by
  constructor
  · intro h
    rw [h 3 (by norm_num)]
  · intro h
    rw [← regularized_initial_identity_full_strip 3 (by norm_num)] at h
    have hall := (single_resolvent_test α).mp h
    let e : ZetaZerosInTraceStrip (1/2) ≃ ZetaZerosInTraceStrip α :=
      { toFun := fun z => ⟨z.val, z.prop.1, z.prop.2.1, z.prop.2.2.1, hall z⟩
        invFun := fun z => ⟨z.val, z.prop.1, z.prop.2.1, z.prop.2.2.1, by
          have h0 := z.prop.2.1
          have h1 := z.prop.2.2.1
          rw [abs_lt]
          constructor <;> linarith⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    intro s hs
    have heq : regularizedSpectral α s = regularizedSpectral (1/2) s :=
      (e.tsum_eq (zeroResolventTerm α s)).symm
    calc
      regularizedTraceRHS α s = regularizedTraceRHS (1/2) s := by
        unfold regularizedTraceRHS
        rw [heq]
      _ = zetaLogDeriv s := regularized_initial_identity_full_strip s hs
