-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Model.rat_finite_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:06:24.802349+00:00
-- url     : https://prove2.me/submissions/e9bec3ad-000a-41b6-871a-3b91382d873b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_exists_finite_place
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_neg_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory.QuadSymbol
open GlobalTheory GlobalTheory.QuadSymbol GlobalTheory.QuadSymbol.Model
namespace GlobalTheory.QuadSymbol.Model
theorem _root_.solution (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), finDiag ℚ (-1) v ∉
      normGroup ℚ (QuadraticAlgebra ℚ (-1) 0) (v.adicCompletion ℚ) := by
  obtain ⟨v, hv⟩ := exists_finite_place (K := ℚ) Rat.infinitePlace Rat.isReal_infinitePlace
    (fun _ => Subsingleton.elim _ _) H
  refine ⟨v, ?_⟩
  convert eta_eq_neg_one_iff.1 hv
  exact Subsingleton.elim _ _
end GlobalTheory.QuadSymbol.Model
