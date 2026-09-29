-- Prove2me | solution 1 for Ideal.exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/59e385b0-33fd-573b-ba87-7f0347a2aa37

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le

set_option autoImplicit false

theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B) (hI : I ≤ I ^ 2)
    (P : Ideal B) [P.IsPrime] (hIP : I ≤ P) :
    ∃ f : B, f ∉ P ∧ ∀ a ∈ I, f * a = 0 := by
  classical
  have hfg : I.FG := (isNoetherianRing_iff_ideal_fg B).1 inferInstance I
  have hle : I ≤ I • I := by
    intro a ha
    have := hI ha
    rwa [pow_two, ← Ideal.smul_eq_mul] at this
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I I hfg hle
  refine ⟨r, ?_, fun a ha => ?_⟩
  · intro hrP
    have h1 : r - (r - 1) ∈ P := P.sub_mem hrP (hIP hr1)
    rw [sub_sub_cancel] at h1
    exact (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top inferInstance) h1
  · have := hr a ha
    rwa [smul_eq_mul] at this

end S_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le
end P2MW
export P2MW.S_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le (solution)
