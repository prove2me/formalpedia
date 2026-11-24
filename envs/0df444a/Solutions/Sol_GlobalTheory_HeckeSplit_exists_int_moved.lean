-- Prove2me | solution 1 for GlobalTheory.HeckeSplit.exists_int_moved
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:47.315563+00:00
-- url     : https://prove2.me/submissions/45f66587-00c4-4a86-bba4-6da24f08b388

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EventuallyResidueDegreeOnePrimeMovedByGalois
import Theorems.Thm_GlobalTheory_HeckeSplit_finPart_infIdele
import Theorems.Thm_GlobalTheory_HeckeSplit_finPart_localIdele
import Theorems.Thm_GlobalTheory_HeckeSplit_infPart_infIdele
import Theorems.Thm_GlobalTheory_HeckeSplit_infPart_localIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HeckeSplit.finPart_infIdele
attribute [local simp] GlobalTheory.HeckeSplit.finPart_localIdele
attribute [local simp] GlobalTheory.HeckeSplit.infPart_infIdele
attribute [local simp] GlobalTheory.HeckeSplit.infPart_localIdele



set_option autoImplicit false
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
open GlobalTheory GlobalTheory.HeckeSplit
namespace GlobalTheory.HeckeSplit
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (hc : c ≠ 1) : ∃ θ : 𝓞 E, c (θ : E) ≠ (θ : E) := by
  by_contra h
  push_neg at h
  apply hc
  ext z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) z
  simp only [map_div₀, AlgEquiv.one_apply]
  exact congrArg₂ (· / ·) (h a) (h b)
end GlobalTheory.HeckeSplit
