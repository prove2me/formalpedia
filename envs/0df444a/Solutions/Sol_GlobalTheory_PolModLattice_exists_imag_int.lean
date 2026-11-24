-- Prove2me | solution 1 for GlobalTheory.PolModLattice.exists_imag_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:08.771969+00:00
-- url     : https://prove2.me/submissions/ce8f62d1-95e7-4738-9377-6f16493d5f05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PolModLattice
theorem _root_.solution : ∃ δ : 𝓞 E, (δ : E) ≠ 0 ∧ bar (δ : E) = -(δ : E) := by
  obtain ⟨x, hx⟩ : ∃ x : E, bar x ≠ x := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => h x)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have key : ∃ c : 𝓞 E, bar (c : E) ≠ c := by
    by_contra h
    push_neg at h
    apply hx
    simp only [bar, map_div₀] at h ⊢
    rw [h a, h b]
  obtain ⟨c, hc⟩ := key
  refine ⟨c - IsCMField.ringOfIntegersComplexConj E c, ?_, ?_⟩
  · simp only [map_sub, IsCMField.coe_ringOfIntegersComplexConj]
    exact sub_ne_zero.2 (Ne.symm hc)
  · simp only [map_sub, IsCMField.coe_ringOfIntegersComplexConj, bar, IsCMField.complexConj_apply_apply]
    ring
end GlobalTheory.PolModLattice
