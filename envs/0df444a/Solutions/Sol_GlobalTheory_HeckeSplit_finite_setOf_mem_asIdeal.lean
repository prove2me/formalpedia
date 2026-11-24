-- Prove2me | solution 1 for GlobalTheory.HeckeSplit.finite_setOf_mem_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:49.42073+00:00
-- url     : https://prove2.me/submissions/cf393597-2a38-4703-92e7-2d1364584724

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] (δ : 𝓞 E) (h : δ ≠ 0) :
    {w : HeightOneSpectrum (𝓞 E) | δ ∈ w.asIdeal}.Finite := by
  have := Ideal.finite_factors (R := 𝓞 E) (I := Ideal.span {δ}) (by simpa using h)
  refine this.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hw
end GlobalTheory.HeckeSplit
