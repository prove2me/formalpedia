-- Prove2me | solution 1 for GlobalTheory.ClassParam.mk_eq_iff_normL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:25.42229+00:00
-- url     : https://prove2.me/submissions/7a8ce7c9-e60a-4513-94e2-badc70fa9911

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
theorem _root_.solution (hP : IsPPol c r P) (x x' : (Lplus hP ⊗[F] k)ˣ) :
    (QuotientGroup.mk x : _ ⧸ normL k hP) = QuotientGroup.mk x' ↔
      ∃ z : (AdjoinRoot P ⊗[F] k)ˣ,
        inclPlus k hP x' = inclPlus k hP x * (z * starLk k hP z) := by
  rw [QuotientGroup.eq, normL, Subgroup.mem_comap, MonoidHom.mem_range]
  refine exists_congr fun z => ?_
  rw [map_mul, map_inv, eq_inv_mul_iff_mul_eq, eq_comm, Units.ext_iff]
  rfl
end GlobalTheory.ClassParam
