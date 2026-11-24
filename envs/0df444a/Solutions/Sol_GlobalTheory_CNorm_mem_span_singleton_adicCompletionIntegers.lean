-- Prove2me | solution 1 for GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:13:14.433084+00:00
-- url     : https://prove2.me/submissions/94d3d777-e53e-4391-8837-11a0c3f360ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {t : v.adicCompletionIntegers F}
    (ht : Valued.v (t : v.adicCompletion F) ≠ 0) (x : v.adicCompletionIntegers F) :
    x ∈ Ideal.span {t} ↔
      Valued.v (x : v.adicCompletion F) ≤ Valued.v (t : v.adicCompletion F) := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    have ha : Valued.v (a : v.adicCompletion F) ≤ 1 := a.2
    change Valued.v ((a : v.adicCompletion F) * t) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' ha
  · intro hx
    have ht1 : (t : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h] at ht; simp at ht
    have hm : (x : v.adicCompletion F) / t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ (zero_lt_iff.2 ht)]
      exact hx
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    change (x : v.adicCompletion F) / t * t = x
    rw [div_mul_cancel₀ _ ht1]
end GlobalTheory.CNorm
