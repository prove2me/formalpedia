-- Prove2me | solution 1 for GlobalTheory.ClassParam.star_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:24.104801+00:00
-- url     : https://prove2.me/submissions/c32b2fe4-b248-4d38-9356-7cd9be596e86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_fixed_tensor

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
theorem _root_.solution (hP : IsPPol c r P) (z : AdjoinRoot P ⊗[F] k) :
    starLk k hP z = z ↔ ∃ w, inclPlus k hP w = z :=
  fixed_tensor k (Lplus hP).val.toLinearMap (starL hP).toLinearMap
    (fun v => ⟨fun h => ⟨⟨v, h⟩, rfl⟩, by rintro ⟨w, rfl⟩; exact w.2⟩) z
end GlobalTheory.ClassParam
