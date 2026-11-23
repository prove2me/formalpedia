-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Model.isQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:21.876349+00:00
-- url     : https://prove2.me/submissions/573a9c85-2604-4f7f-bba5-560042f84609

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
theorem _root_.solution :
    Algebra.IsQuadraticExtension K (QuadraticAlgebra K d 0) :=
  ⟨QuadraticAlgebra.finrank_eq_two d 0⟩
end _root_.GlobalTheory.QuadSymbol.Model
end GlobalTheory.QuadSymbol.Model
