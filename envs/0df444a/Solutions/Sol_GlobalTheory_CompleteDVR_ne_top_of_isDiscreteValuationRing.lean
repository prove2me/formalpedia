-- Prove2me | solution 1 for GlobalTheory.CompleteDVR.ne_top_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:07.374836+00:00
-- url     : https://prove2.me/submissions/6ae924c2-ea0d-4571-8c03-37077bd87fd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing HeightOneSpectrum
open GlobalTheory GlobalTheory.CompleteDVR
namespace GlobalTheory.CompleteDVR
theorem _root_.solution {K : Type} [Field K] (V : ValuationSubring K)
    [IsDiscreteValuationRing V] : V ≠ ⊤ := by
  intro h
  have hall : ∀ y : K, y ∈ V := fun y => h ▸ ValuationSubring.mem_top y
  apply IsDiscreteValuationRing.not_a_field V
  ext x
  simp only [Ideal.mem_bot]
  constructor
  · intro hx
    by_contra hne
    have hne' : (x : K) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    apply (IsLocalRing.mem_maximalIdeal x).1 hx
    refine IsUnit.of_mul_eq_one ⟨(x : K)⁻¹, hall _⟩ (Subtype.ext ?_)
    simp [hne']
  · rintro rfl
    exact Ideal.zero_mem _
end GlobalTheory.CompleteDVR
