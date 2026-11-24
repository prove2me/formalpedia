-- Prove2me | solution 1 for GlobalTheory.ValuationExtensionExistence.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:09.999856+00:00
-- url     : https://prove2.me/submissions/f26ce706-0f82-4d24-a5cd-6739abea67a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherLast
import Theorems.Thm_GlobalTheory_ValuationExtensionExistence_exists_extension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuationExtensionExistence
namespace GlobalTheory.ValuationExtensionExistence
theorem _root_.solution : ∀ (V R K : Type) [inst : CommRing V] [IsDomain V] [IsLocalRing V]
    [inst_3 : CommRing R] [IsDomain R] [IsLocalRing R] [inst_6 : Field K] [IsAlgClosed K]
    (ρ : V →+* R), Function.Injective (⇑ρ : V → R) → RingHom.Finite ρ →
      IsLocalHom ρ ∧ ∀ (ev : V →+* K), ∃ (ev₁ : R →+* K), RingHom.comp ev₁ ρ = ev := by
  intro V R K _ _ _ _ _ _ _ _ ρ hinj hfin
  have hint : ρ.IsIntegral := hfin.to_isIntegral
  refine ⟨?_, fun ev => ?_⟩
  · refine ((IsLocalRing.local_hom_TFAE ρ).out 4 0).mp ?_
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ρ hint _)
  · let := ρ.toAlgebra
    have : Algebra.IsIntegral V R := ⟨hint⟩
    have : FaithfulSMul V R := (faithfulSMul_iff_algebraMap_injective V R).2 hinj
    exact exists_extension ev
end GlobalTheory.ValuationExtensionExistence
