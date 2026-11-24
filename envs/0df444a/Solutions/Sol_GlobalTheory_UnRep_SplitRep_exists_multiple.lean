-- Prove2me | solution 1 for GlobalTheory.UnRep.SplitRep.exists_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:00.348022+00:00
-- url     : https://prove2.me/submissions/56d5df3b-a28c-4c46-96b3-17aca07c155f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
namespace GlobalTheory.UnRep.SplitRep
namespace _root_.GlobalTheory.UnRep.SplitRep
theorem _root_.solution (s : 𝓞 E) (hs : s ≠ 0) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ s ∣ algebraMap (𝓞 F) (𝓞 E) m ∧ ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal →
      ∃ P : Ideal (𝓞 E), P.IsPrime ∧ s ∈ P ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
  classical
  set J := Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {s}) with hJdef
  have hJ : J ≠ ⊥ := Ideal.comap_ne_bot_of_integral_mem hs (Ideal.mem_span_singleton_self s)
    (Algebra.IsIntegral.isIntegral s)
  have hJ0 : J ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero hJ
  set h := Fintype.card (ClassGroup (𝓞 F))
  have hprin : (J ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hJ0 h)]
    have : ClassGroup.mk0 (⟨J, hJ0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact this
  set m := Submodule.IsPrincipal.generator (J ^ h)
  have hspan : J ^ h = Ideal.span {m} := (Submodule.IsPrincipal.span_singleton_generator _).symm
  have hmJ : m ∈ J := Ideal.pow_le_self (Fintype.card_ne_zero) (hspan ▸ Ideal.mem_span_singleton_self m)
  refine ⟨m, ?_, ?_, ?_⟩
  · intro hm0
    apply pow_ne_zero h hJ
    rw [hspan, hm0, Ideal.span_singleton_eq_bot.2 rfl]
    rfl
  · exact Ideal.mem_span_singleton.1 hmJ
  · intro v hv
    have hle : J ≤ v.asIdeal := by
      apply v.isPrime.le_of_pow_le (n := h)
      rw [hspan, Ideal.span_le, Set.singleton_subset_iff]
      exact hv
    obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (Ideal.span {s}) hle
    exact ⟨Q, hQp, hQ (Ideal.mem_span_singleton_self s), hQc⟩
end _root_.GlobalTheory.UnRep.SplitRep
end GlobalTheory.UnRep.SplitRep
