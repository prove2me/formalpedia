-- Prove2me | solution 1 for MIPStarRE.Quantum.ProjectorRangeONB.subprojector_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:38:13.103473+00:00
-- url     : https://prove2.me/submissions/be96c84e-699a-4886-ad05-922361bc94ff

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/ProjectorONB.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/ProjectorONB.lean (solution of MIPStarRE.Quantum.ProjectorRangeONB.subprojector_idempotent);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.Quantum.ProjectorRangeONB
noncomputable section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Op ι} {hP : IsProj P} (b : ProjectorRangeONB P hP)
omit [DecidableEq ι] in
/-- Rank-one projectors from an orthonormal family multiply as Kronecker deltas. -/
lemma rankOne_mul (i j : Fin P.rank) :
    b.rankOne i * b.rankOne j = if i = j then b.rankOne i else 0 := by
  rw [rankOne, rankOne, Matrix.vecMulVec_mul_vecMulVec]
  have horth := b.orthonormal i j
  by_cases hij : i = j
  · subst hij
    rw [horth]
    simp
  · have hzero : star (b.vec i) ⬝ᵥ b.vec j = 0 := by simpa [hij] using horth
    rw [hzero]
    simp [hij]
end
end MIPStarRE.Quantum.ProjectorRangeONB

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.Quantum.ProjectorRangeONB
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Op ι} {hP : IsProj P} (b : ProjectorRangeONB P hP)
omit [DecidableEq ι] in
theorem _root_.solution (S : Finset (Fin P.rank)) :
    b.subprojector S * b.subprojector S = b.subprojector S := by
  classical
  unfold subprojector
  calc
    (∑ i ∈ S, b.rankOne i) * (∑ j ∈ S, b.rankOne j)
        = ∑ i ∈ S, ∑ j ∈ S, b.rankOne i * b.rankOne j := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ i ∈ S, b.rankOne i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.sum_eq_single i]
          · rw [b.rankOne_mul i i]
            simp
          · intro j hj hji
            have hij : i ≠ j := fun hij => hji hij.symm
            rw [b.rankOne_mul i j]
            simp [hij]
          · intro hi_not
            exact False.elim (hi_not hi)
end MIPStarRE.Quantum.ProjectorRangeONB
