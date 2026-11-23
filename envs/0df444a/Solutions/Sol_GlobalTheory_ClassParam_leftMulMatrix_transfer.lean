-- Prove2me | solution 1 for GlobalTheory.ClassParam.leftMulMatrix_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:27.879275+00:00
-- url     : https://prove2.me/submissions/07356d1d-7ee6-4618-9f62-0d7ef75f5e03

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
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R S]
  [Algebra A B] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ClassParam
theorem _root_.solution (f : R →+* A) (ψ : S →+* B)
    (h : ∀ a, ψ (algebraMap R S a) = algebraMap A B (f a)) (b : Module.Basis ι R S)
    (b' : Module.Basis ι A B) (hb : ∀ i, ψ (b i) = b' i) (x : S) :
    Algebra.leftMulMatrix b' (ψ x) = (Algebra.leftMulMatrix b x).map f := by
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    ← hb, ← map_mul]
  generalize x * b j = y
  conv_lhs => rw [← b.sum_repr y]
  simp only [map_sum, Algebra.smul_def, map_mul, h, hb]
  simp only [← Algebra.smul_def, map_smul, Module.Basis.repr_self]
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
end GlobalTheory.ClassParam
