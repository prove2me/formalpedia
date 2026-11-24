-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.alpha_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:20.163155+00:00
-- url     : https://prove2.me/submissions/39bf437e-d2d5-4344-8321-35be376fb850

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
theorem _root_.solution (hP : IsPPol c r P) : (alpha hP : AdjoinRoot P) = AdjoinRoot.root P := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
