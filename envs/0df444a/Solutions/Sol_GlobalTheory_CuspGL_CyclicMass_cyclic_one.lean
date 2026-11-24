-- Prove2me | solution 1 for GlobalTheory.CuspGL.CyclicMass.cyclic_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:02:47.823133+00:00
-- url     : https://prove2.me/submissions/3c981d68-3349-4d4a-a002-cc15a660fa49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.CyclicMass
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL.CyclicMass
theorem _root_.solution (D : F[X]) (U : Submodule F (AdjoinRoot D))
    (hU : ∀ a ∈ U, AdjoinRoot.root D * a ∈ U) (h1 : (1 : AdjoinRoot D) ∈ U) : U = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  induction p using Polynomial.induction_on with
  | C a =>
    have : AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]; exact U.smul_mem _ h1
  | add p q hp hq => rw [map_add]; exact U.add_mem (hp trivial) (hq trivial)
  | monomial n a ih =>
    have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [this, map_mul, AdjoinRoot.mk_X]
    exact hU _ (ih trivial)
end GlobalTheory.CuspGL.CyclicMass
