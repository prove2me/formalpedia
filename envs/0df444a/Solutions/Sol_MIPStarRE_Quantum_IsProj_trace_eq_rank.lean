-- Prove2me | solution 1 for MIPStarRE.Quantum.IsProj.trace_eq_rank
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:38:12.330249+00:00
-- url     : https://prove2.me/submissions/0f734408-1f26-4593-9d2d-118480c2c9a3

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/ProjectorONB.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/ProjectorONB.lean (solution of MIPStarRE.Quantum.IsProj.trace_eq_rank);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.Quantum.IsProj
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem _root_.solution (Q : Op ι) (hQ : IsProj Q) :
    Q.trace = (Q.rank : ℂ) := by
  classical
  let p : ι → Prop := fun i => hQ.isSelfAdjoint.isHermitian.eigenvalues i ≠ 0
  let indicator : ι → ℕ := fun i => if p i then 1 else 0
  have hp_nat : Fintype.card {i // p i} = ∑ i, indicator i := by
    rw [Fintype.card_subtype p]
    simpa [p, indicator] using Finset.card_filter p (Finset.univ : Finset ι)
  have hp_complex : (Fintype.card {i // p i} : ℂ) = ∑ i, (indicator i : ℂ) := by
    exact_mod_cast hp_nat
  have h_indicator : ∀ i, (indicator i : ℂ) = (hQ.isSelfAdjoint.isHermitian.eigenvalues i : ℂ) := by
    intro i
    rcases hQ.eigenvalues_zero_or_one Q i with hzero | hone
    · simp [p, indicator, hzero]
    · simp [p, indicator, hone]
  calc
    Q.trace = ∑ i, (hQ.isSelfAdjoint.isHermitian.eigenvalues i : ℂ) :=
      hQ.isSelfAdjoint.isHermitian.trace_eq_sum_eigenvalues
    _ = ∑ i, (indicator i : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          symm
          exact h_indicator i
    _ = Fintype.card {i // p i} := by symm; exact hp_complex
    _ = (Q.rank : ℂ) := by rw [hQ.isSelfAdjoint.isHermitian.rank_eq_card_non_zero_eigs]
end MIPStarRE.Quantum.IsProj
