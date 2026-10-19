-- Prove2me | solution 1 for MIPStarRE.Quantum.ProjectorRangeONB.subprojector_isProj
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:39:52.78737+00:00
-- url     : https://prove2.me/submissions/01d0a72f-977d-4416-8643-c06188d3485f

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/ProjectorONB.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/ProjectorONB.lean (solution of MIPStarRE.Quantum.ProjectorRangeONB.subprojector_isProj);
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
import Theorems.Thm_MIPStarRE_Quantum_ProjectorRangeONB_subprojector_idempotent

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
/-- A selected sum of orthonormal rank-one projectors is Hermitian. -/
lemma subprojector_isHermitian (S : Finset (Fin P.rank)) :
    (b.subprojector S).IsHermitian := by
  classical
  unfold subprojector rankOne
  rw [Matrix.IsHermitian]
  simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_vecMulVec]
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
    IsProj (b.subprojector S) where
  isIdempotentElem := b.subprojector_idempotent S
  isSelfAdjoint := (b.subprojector_isHermitian S).isSelfAdjoint
end MIPStarRE.Quantum.ProjectorRangeONB
