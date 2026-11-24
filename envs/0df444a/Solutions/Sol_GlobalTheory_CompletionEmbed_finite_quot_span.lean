-- Prove2me | solution 1 for GlobalTheory.CompletionEmbed.finite_quot_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:18:03.881867+00:00
-- url     : https://prove2.me/submissions/9538abc6-164c-43b2-8e52-1f19187101e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteOfFiniteQuotMapOfIsPrecomplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePadicIntDomainEmbedding
import Theorems.Thm_GlobalTheory_CompletionEmbed_exists_pow_le_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompletionEmbed
variable (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsLocalRing C]
namespace GlobalTheory.CompletionEmbed
theorem _root_.solution [IsNoetherianRing C] [Finite (ResidueField C)] (hp0 : (p : C) ≠ 0)
    (hprime : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) :
    Finite (AdicCompletion (maximalIdeal C) C ⧸
      Ideal.span {(p : AdicCompletion (maximalIdeal C) C)}) := by
  set A := AdicCompletion (maximalIdeal C) C
  have fg : (maximalIdeal C).FG := IsNoetherian.noetherian _
  haveI : Finite (C ⧸ maximalIdeal C) := ‹Finite (ResidueField C)›
  haveI : Finite (A ⧸ (maximalIdeal C).map (algebraMap C A)) := by
    have h := Finite.of_injective _
      (RingHom.kerLift_injective (AdicCompletion.evalOneₐ (maximalIdeal C)).toRingHom)
    rw [AdicCompletion.ker_evalOneₐ_eq_map _ fg] at h
    exact h
  obtain ⟨N, hN⟩ := exists_pow_le_span p C hp0 hprime
  haveI : Finite (A ⧸ ((maximalIdeal C).map (algebraMap C A)) ^ N) :=
    Ideal.finite_quotient_pow (fg.map _) N
  have hle : ((maximalIdeal C).map (algebraMap C A)) ^ N ≤ Ideal.span {(p : A)} := by
    rw [← Ideal.map_pow]
    calc _ ≤ (Ideal.span {(p : C)}).map (algebraMap C A) := Ideal.map_mono hN
      _ = _ := by rw [Ideal.map_span, Set.image_singleton, map_natCast]
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
end GlobalTheory.CompletionEmbed
