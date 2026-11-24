-- Prove2me | solution 1 for GlobalTheory.DenominatorOfSpan.exists_smul_mem_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:22.465877+00:00
-- url     : https://prove2.me/submissions/8904f7a0-b758-47bf-9b56-489fa8ca675f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmulMemOfSpanEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DenominatorOfSpan
open GlobalTheory.UnitLemma
namespace GlobalTheory.DenominatorOfSpan
theorem _root_.solution {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup A] [Module E A] [Module O A] [IsScalarTower O E A]
    (L : Submodule O A) (hL : Submodule.span E (L : Set A) = ⊤) (x : A) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set A) := by rw [hL]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hay
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul e y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors O) e
    have hs' : e * algebraMap O E (s : O) = algebraMap O E n := hs
    refine ⟨a * (s : O), mul_ne_zero ha (nonZeroDivisors.ne_zero s.2), ?_⟩
    have h1 : (s : O) • e • y = n • y := by
      rw [← algebraMap_smul E (s : O), ← mul_smul, mul_comm, hs', algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.smul_mem n hay
end GlobalTheory.DenominatorOfSpan
