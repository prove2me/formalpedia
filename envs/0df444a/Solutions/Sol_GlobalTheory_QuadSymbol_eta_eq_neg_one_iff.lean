-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.eta_eq_neg_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:31.577211+00:00
-- url     : https://prove2.me/submissions/50c48967-5d12-4962-9746-60926b68785b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory

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
open scoped TensorProduct
open GlobalTheory GlobalTheory.QuadSymbol
variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable {K L}
open NumberField IsDedekindDomain
open scoped TensorProduct
variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable {K L}
namespace GlobalTheory.QuadSymbol
namespace _root_.GlobalTheory.QuadSymbol
theorem _root_.solution {A : Type} [CommRing A] [Algebra K A] {x : Aˣ} :
    _root_.GlobalTheory.QuadSymbol.eta K L A x = -1 ↔ x ∉ _root_.GlobalTheory.QuadSymbol.normGroup K L A := by
  unfold _root_.GlobalTheory.QuadSymbol.eta
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    decide
  · simp [h]
end _root_.GlobalTheory.QuadSymbol
end GlobalTheory.QuadSymbol
