-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Model.numberField
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:20.199221+00:00
-- url     : https://prove2.me/submissions/c67035d2-5e98-4f42-aec2-c55ac345df77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo

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
open NumberField IsDedekindDomain
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]
namespace GlobalTheory.QuadSymbol.Model
namespace _root_.GlobalTheory.QuadSymbol.Model
theorem _root_.solution [NumberField K] :
    NumberField (QuadraticAlgebra K d 0) := by
  haveI : Module.Finite ℚ (QuadraticAlgebra K d 0) := Module.Finite.trans K _
  exact ⟨⟩
end _root_.GlobalTheory.QuadSymbol.Model
end GlobalTheory.QuadSymbol.Model
