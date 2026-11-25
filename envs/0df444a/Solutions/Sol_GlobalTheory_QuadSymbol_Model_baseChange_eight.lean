-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Model.baseChange_eight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:06:17.32598+00:00
-- url     : https://prove2.me/submissions/714262ed-122b-479d-a92f-0b18dd943d64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_numberField
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_baseChange_sqrt
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_neg_one_not_sq_sqrt_two

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
    ∃ _ : Fact (∀ r : QuadraticAlgebra ℚ 2 0,
        r ^ 2 ≠ algebraMap ℚ (QuadraticAlgebra ℚ 2 0) (-1) + 0 * r),
      ∀ v : HeightOneSpectrum (𝓞 ℚ), BaseChangeAt ℚ (QuadraticAlgebra ℚ (-1) 0) (QuadraticAlgebra ℚ 2 0)
        (QuadraticAlgebra (QuadraticAlgebra ℚ 2 0) (algebraMap ℚ (QuadraticAlgebra ℚ 2 0) (-1)) 0)
        (v.adicCompletion ℚ) := by
  have := numberField (2 : ℚ)
  have hF : Fact (∀ r : QuadraticAlgebra ℚ 2 0,
      r ^ 2 ≠ algebraMap ℚ (QuadraticAlgebra ℚ 2 0) (-1) + 0 * r) :=
    ⟨fun r => by rw [map_neg, map_one]; exact neg_one_not_sq_sqrt_two r⟩
  refine ⟨hF, fun v => ?_⟩
  convert (baseChange_sqrt (F := ℚ) (K := QuadraticAlgebra ℚ 2 0) (-1) H).1 v <;>
    exact Subsingleton.elim _ _
end GlobalTheory.QuadSymbol.Model
