-- Prove2me | solution 1 for GlobalTheory.ClassParam.exists_pow_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:08.2767+00:00
-- url     : https://prove2.me/submissions/05106c97-7e17-4d96-b5a1-1c352480e594

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
theorem _root_.solution (hP : IsPPol c r P) : ∃ b : Module.Basis (Fin r) E (AdjoinRoot P),
    (∀ i, b i = AdjoinRoot.root P ^ (i : ℕ)) ∧
      (Algebra.leftMulMatrix b (AdjoinRoot.root P)).charpoly = P := by
  obtain ⟨h1, h2, rfl, -⟩ := hP
  refine ⟨(AdjoinRoot.powerBasis' h1).basis, (AdjoinRoot.powerBasis' h1).basis_eq_pow, ?_⟩
  refine (charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h1)).trans ?_
  show minpoly E (AdjoinRoot.root P) = P
  rw [AdjoinRoot.minpoly_root h1.ne_zero, h1.leadingCoeff]
  simp
end GlobalTheory.ClassParam
