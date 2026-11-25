-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Model.eta_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:06:19.470245+00:00
-- url     : https://prove2.me/submissions/472b2142-e9ba-47e4-b70f-87f3696e049b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_mem_normGroup_sqrt
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_one_iff


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
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]
namespace GlobalTheory.QuadSymbol.Model
theorem _root_.solution {A : Type} [Field A] [Algebra K A] (h2 : (2 : A) ≠ 0) {s : A} (hs0 : s ≠ 0)
    (hs : s ^ 2 = algebraMap K A d) (x : Aˣ) : eta K (QuadraticAlgebra K d 0) A x = 1 := by
  rw [eta_eq_one_iff, mem_normGroup_sqrt]
  refine ⟨(x + 1) / 2, (x - 1) / (2 * s), ?_⟩
  rw [← hs]
  field_simp
  ring
end GlobalTheory.QuadSymbol.Model
