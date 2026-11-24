-- Prove2me | solution 1 for GlobalTheory.EigenPair.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:44:40.127067+00:00
-- url     : https://prove2.me/submissions/c10605cb-719f-473b-8c33-1f0754836348

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFifth
import Theorems.Thm_GlobalTheory_EigenPair_natMul_mem_orderC
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
open GlobalTheory GlobalTheory.EigenPair
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.EigenPair
theorem _root_.solution {K : Type} [Field K] [CharZero K] (c : Ideal (OF E)) (hc : c ≠ ⊥) (σ σ' : E →+* K)
    (h : σ' ≠ bar σ) : ∃ a b : orderC c, (b : E) = IsCMField.complexConj E a ∧ σ a ≠ σ' b := by
  by_contra hn
  push_neg at hn
  have hm : ((Ideal.absNorm c : ℕ) : K) ≠ 0 := by
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.1 hc)
  have hz : ∀ z : 𝓞 E, σ (z : E) = σ' (IsCMField.complexConj E (z : E)) := by
    intro z
    have h1 := hn ⟨_, natMul_mem_orderC c z⟩
      ⟨_, natMul_mem_orderC c (IsCMField.ringOfIntegersComplexConj E z)⟩
      (by simp [IsCMField.coe_ringOfIntegersComplexConj])
    simp only [map_mul, map_natCast, IsCMField.coe_ringOfIntegersComplexConj] at h1
    exact mul_left_cancel₀ hm h1
  have heq : σ = bar σ' := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_
    ext z
    exact hz z
  apply h
  rw [heq]
  ext x
  simp [bar, IsCMField.complexConj_apply_apply]
end GlobalTheory.EigenPair
