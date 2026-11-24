-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.classParam_of_CM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:21.974632+00:00
-- url     : https://prove2.me/submissions/0c55fe56-d056-450b-b4a8-7a863dbfeb84

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix NumberField IsDedekindDomain Formalism.UG
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
variable (k : Type) [Field k] [Algebra F k]
attribute [local instance] algLk
variable {k}
variable (k)
namespace GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
theorem _root_.solution (h : ClassParamCM) : ClassParam :=
  fun F E _ _ _ _ _ h1 h2 h3 _ c hc r _ P hP => h F E h1 h2 h3 c hc r P hP
end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
