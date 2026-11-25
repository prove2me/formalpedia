-- Prove2me | solution 1 for GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:19.778142+00:00
-- url     : https://prove2.me/submissions/98165796-86b1-4903-8f46-562b98380463

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulLe
import Theorems.Thm_GlobalTheory_IntegerMultipleIntegral_exists_int_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegerMultipleIntegral
namespace GlobalTheory.IntegerMultipleIntegral
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    {B : Submodule (NumberField.RingOfIntegers K) V} (hB : B.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ B, N • x ∈ A := by
  obtain ⟨s, rfl⟩ := hB
  choose f hf0 hf using exists_int_smul_mem hA
  refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.mpr fun y _ => hf0 y, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.mp hy)
    rw [hc, mul_comm, mul_smul]
    exact A.toAddSubgroup.zsmul_mem (hf y) c
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact A.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact A.smul_mem a hy
end GlobalTheory.IntegerMultipleIntegral
