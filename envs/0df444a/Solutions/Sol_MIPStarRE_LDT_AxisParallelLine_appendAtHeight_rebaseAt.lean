-- Prove2me | solution 1 for MIPStarRE.LDT.AxisParallelLine.appendAtHeight_rebaseAt
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:29:35.106377+00:00
-- url     : https://prove2.me/submissions/9a175fdd-a7fe-4dc3-8890-a2267b76bb46

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/AxisParallelLine.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/AxisParallelLine.lean (solution of MIPStarRE.LDT.AxisParallelLine.appendAtHeight_rebaseAt);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.AxisParallelLine
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t x : Fq params) :
    appendAtHeight params (rebaseAt ℓ t) x =
      rebaseAt (appendAtHeight params ℓ x) t := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             appendPoint params
               (({ base := base, direction := direction } : AxisParallelLine params).pointAt t) x,
           direction := embedCoord params direction } : AxisParallelLine params.next) =
        ({ base :=
             ({ base := appendPoint params base x,
                direction := embedCoord params direction } :
                AxisParallelLine params.next).pointAt t,
           direction := embedCoord params direction } : AxisParallelLine params.next)
      congr
      funext i
      by_cases hdir : i = embedCoord params direction
      · subst i
        simp [appendPoint, pointAt, embedCoord]
        try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
      · by_cases hi : i.1 < params.m
        · have hdir' : (⟨i.1, hi⟩ : Fin params.m) ≠ direction := by
            intro h
            apply hdir
            apply Fin.ext
            simpa [embedCoord] using congrArg Fin.val h
          simp [appendPoint, pointAt, hi, hdir, hdir']
        · simp [appendPoint, pointAt, hi, hdir]
end MIPStarRE.LDT.AxisParallelLine
