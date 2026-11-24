-- Prove2me | solution 1 for GlobalTheory.ClassParam.inclPlus_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:23.450021+00:00
-- url     : https://prove2.me/submissions/c2537f4a-5698-461e-bd4c-f5ddf8302408

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution (hP : IsPPol c r P) : Function.Injective (inclPlus k hP) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := k) (Lplus hP).val.toLinearMap
    Subtype.val_injective
end GlobalTheory.ClassParam
