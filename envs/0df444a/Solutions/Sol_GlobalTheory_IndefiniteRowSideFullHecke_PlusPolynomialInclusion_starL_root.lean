-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.starL_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:06.567805+00:00
-- url     : https://prove2.me/submissions/cdeae38a-5158-48e9-8a0f-692f0a92427b

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
theorem _root_.solution (hP : IsPPol c r P) :
    starL hP (AdjoinRoot.root P) = ((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) := by
  simp [starL]
end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
