-- Prove2me | solution 1 for GlobalTheory.CoprimeBasis.isTorsionFree_of_addTorsionFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:58:39.037564+00:00
-- url     : https://prove2.me/submissions/3558d7bb-834a-4f1d-b682-4f71aef206b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIndependentBasisCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.CoprimeBasis
namespace GlobalTheory.CoprimeBasis
theorem _root_.solution {F : Type} [Field F] [NumberField F]
    (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [IsAddTorsionFree M] :
    Module.IsTorsionFree (𝓞 F) M where
  isSMulRegular r hr x y hxy := by
    have hxy' : r • x = r • y := hxy
    have hr0 : r ≠ 0 := hr.ne_zero
    have hn : Ideal.absNorm (Ideal.span {r}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hr0
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
    have h1 : (Ideal.absNorm (Ideal.span {r})) • (x - y) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 F), ← hb, mul_smul, smul_sub, hxy', sub_self, smul_zero]
    exact sub_eq_zero.1 (nsmul_right_injective hn (h1.trans (nsmul_zero _).symm))
end GlobalTheory.CoprimeBasis
