-- Prove2me | solution 1 for GlobalTheory.InertField.exists_not_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:45.269473+00:00
-- url     : https://prove2.me/submissions/258f13b2-3857-444d-b604-1b0275601dac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
open GlobalTheory GlobalTheory.InertField
open scoped TensorProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
namespace GlobalTheory.InertField
namespace _root_.GlobalTheory.InertField
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 E, ∀ r : 𝓞 F, a - algebraMap (𝓞 F) (𝓞 E) r ∉ v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) := by
  by_contra hcon
  push_neg at hcon
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hrank := Ideal.finrank_quotient_map v.asIdeal F E (S := 𝓞 E)
  rw [h2] at hrank
  have hle : Module.finrank (𝓞 F ⧸ v.asIdeal)
      (𝓞 E ⧸ v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) ≤ 1 := by
    apply finrank_le_one 1
    intro w
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨r, hr⟩ := hcon a
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_quotient_map_quotient,
      Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact hr
  omega
end _root_.GlobalTheory.InertField
end GlobalTheory.InertField
