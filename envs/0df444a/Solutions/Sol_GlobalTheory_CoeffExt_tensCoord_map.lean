-- Prove2me | solution 1 for GlobalTheory.CoeffExt.tensCoord_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:14.614904+00:00
-- url     : https://prove2.me/submissions/9cb46d32-cffd-4967-befe-cdc2f22c5c5d

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {Qp : Type} [Field Qp] {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
  [Algebra Qp LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  [Module LL' V'] [IsScalarTower Qp LL' V']
  {ι : Type} [Fintype ι] [DecidableEq ι] (E : V' ≃ₗ[LL] (ι → V))
namespace GlobalTheory.CoeffExt
theorem _root_.solution {C D : Type} [AddCommGroup C] [Module Qp C] [AddCommGroup D] [Module Qp D]
    (φ' : V' →ₗ[LL'] V') (φ : V →ₗ[LL] V) (h : ∀ x i, E (φ' x) i = φ (E x i)) (ψ : C →ₗ[Qp] D)
    (x : V' ⊗[Qp] C) (i : ι) :
    tensCoord E D (AlgebraTensorModule.map φ' ψ x) i =
      AlgebraTensorModule.map φ ψ (tensCoord E C x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [h]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
end GlobalTheory.CoeffExt
