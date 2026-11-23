-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.starL_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:32.189131+00:00
-- url     : https://prove2.me/submissions/a9eac25f-b6e7-4625-8dbb-90e9761befcd

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
theorem _root_.solution (hP : IsPPol c r P) (e : E) :
    starL hP (AdjoinRoot.of P e) = AdjoinRoot.of P (c e) := by
  simp [starL]
end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
