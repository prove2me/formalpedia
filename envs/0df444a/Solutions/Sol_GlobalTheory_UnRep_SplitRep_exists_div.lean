-- Prove2me | solution 1 for GlobalTheory.UnRep.SplitRep.exists_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:44:59.37544+00:00
-- url     : https://prove2.me/submissions/9f4f2954-0cbe-4e4d-abf5-1a0670723568

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport
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
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SplitRep
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable [NumberField E]
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable [NumberField E]
omit [NumberField E]
namespace GlobalTheory.UnRep.SplitRep
namespace _root_.GlobalTheory.UnRep.SplitRep
theorem _root_.solution (m : 𝓞 F) (hm : m ≠ 0) (e : FiniteAdeleRing (𝓞 F) F)
    (h1 : ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal → e v = 1)
    (h0 : ∀ v : HeightOneSpectrum (𝓞 F), m ∉ v.asIdeal → e v = 0) :
    ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ (m : F) • a = 1 - e := by
  have hmF : (m : F) ≠ 0 := by simpa using hm
  refine ⟨(m : F)⁻¹ • (1 - e), fun v => ?_, ?_⟩
  · show (((m : F)⁻¹ : F) : v.adicCompletion F) * (1 - e v) ∈ v.adicCompletionIntegers F
    by_cases hv : m ∈ v.asIdeal
    · rw [h1 v hv, sub_self, mul_zero]
      exact zero_mem _
    · rw [h0 v hv, sub_zero, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]
      simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuation_of_algebraMap]
      rw [(HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v m).mpr hv, inv_one]
  · rw [smul_smul, mul_inv_cancel₀ hmF, one_smul]
end _root_.GlobalTheory.UnRep.SplitRep
end GlobalTheory.UnRep.SplitRep
