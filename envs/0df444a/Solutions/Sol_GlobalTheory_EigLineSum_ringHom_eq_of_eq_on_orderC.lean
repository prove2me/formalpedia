-- Prove2me | solution 1 for GlobalTheory.EigLineSum.ringHom_eq_of_eq_on_orderC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:24:58.120506+00:00
-- url     : https://prove2.me/submissions/d303a762-d3cd-4fce-8212-e69f351d1f9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFirst
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
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.EigLineSum
namespace GlobalTheory.EigLineSum
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K]
    {c : Ideal (OF E)} (hc : c ≠ ⊥) {σ σ' : E →+* K} (h : ∀ a : orderC c, σ a = σ' a) : σ = σ' := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  set b' : 𝓞 E := algebraMap (OF E) (𝓞 E) b with hb'
  have hb'0 : algebraMap (𝓞 E) E b' ≠ 0 := by
    have : algebraMap (𝓞 E) E b' = algebraMap (OF E) E b := rfl
    rw [this]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (OF E) E)).2 hb0
  have hmem : ∀ z : 𝓞 E, algebraMap (𝓞 E) E (b' * z) ∈ orderC c := fun z =>
    Subring.subset_closure (Or.inr ⟨b' * z, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb), rfl⟩)
  have hb'mem : algebraMap (𝓞 E) E b' ∈ orderC c := by simpa using hmem 1
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun z => ?_)
  have h1 : σ (algebraMap (𝓞 E) E (b' * z)) = σ' (algebraMap (𝓞 E) E (b' * z)) := h ⟨_, hmem z⟩
  have h2 : σ (algebraMap (𝓞 E) E b') = σ' (algebraMap (𝓞 E) E b') := h ⟨_, hb'mem⟩
  have h3 : σ (algebraMap (𝓞 E) E b') ≠ 0 := (map_ne_zero σ).2 hb'0
  simp only [map_mul] at h1
  rw [h2] at h1 h3
  simpa using mul_left_cancel₀ h3 h1
end GlobalTheory.EigLineSum
