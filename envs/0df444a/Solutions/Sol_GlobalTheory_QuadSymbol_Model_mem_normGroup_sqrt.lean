-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:22.497893+00:00
-- url     : https://prove2.me/submissions/e45b2819-1b35-4f17-8655-10c78b5cd1cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
import Theorems.Thm_GlobalTheory_QuadSymbol_mem_normGroup_iff_form


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
theorem _root_.solution {A : Type} [CommRing A] [Algebra K A] {x : Aˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K (QuadraticAlgebra K d 0) A ↔
      ∃ a b : A, (x : A) = a ^ 2 - algebraMap K A d * b ^ 2 := by
  refine _root_.GlobalTheory.QuadSymbol.mem_normGroup_iff_form (QuadraticAlgebra.basis d 0) ?_ ?_
  · ext <;> simp [QuadraticAlgebra.basis] <;> rfl
  · ext <;> simp [QuadraticAlgebra.basis]
end _root_.GlobalTheory.QuadSymbol.Model
end GlobalTheory.QuadSymbol.Model
