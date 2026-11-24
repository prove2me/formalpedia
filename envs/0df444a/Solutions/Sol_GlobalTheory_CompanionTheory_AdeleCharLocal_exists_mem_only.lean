-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.exists_mem_only
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:26:23.253209+00:00
-- url     : https://prove2.me/submissions/bf09e5a3-0529-4bce-9468-d36a96531dcb

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
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
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ t ∈ v.asIdeal ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → t ∉ w.asIdeal := by
  classical
  let P : (Ideal (𝓞 F))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have h1 : ClassGroup.mk0 (P ^ Fintype.card (ClassGroup (𝓞 F))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨t, ht⟩ := (ClassGroup.mk0_eq_one_iff (P ^ Fintype.card (ClassGroup (𝓞 F))).2).1 h1
  have ht' : v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) = Ideal.span {t} := ht
  refine ⟨t, ?_, ?_, fun w hw hm => hw ?_⟩
  · rintro rfl
    exact pow_ne_zero _ v.ne_bot (by rw [ht']; simp)
  · exact Ideal.pow_le_self Fintype.card_ne_zero (ht' ▸ Ideal.mem_span_singleton_self t)
  · have h2 : v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) ≤ w.asIdeal := by
      rw [ht', Ideal.span_singleton_le_iff_mem]; exact hm
    have h3 := w.isPrime.le_of_pow_le h2
    exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h3).symm
end GlobalTheory.CompanionTheory.AdeleCharLocal
