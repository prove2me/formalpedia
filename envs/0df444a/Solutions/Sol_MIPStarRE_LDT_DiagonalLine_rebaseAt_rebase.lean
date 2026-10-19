-- Prove2me | solution 1 for MIPStarRE.LDT.DiagonalLine.rebaseAt_rebase
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:29:35.836872+00:00
-- url     : https://prove2.me/submissions/324a654f-823a-4257-8ead-038379153b9e

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/DiagonalLine.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/DiagonalLine.lean (solution of MIPStarRE.LDT.DiagonalLine.rebaseAt_rebase);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.DiagonalLine
section
set_option backward.isDefEq.respectTransparency false
theorem rebaseAt_pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t s : Fq params) :
    (rebaseAt ℓ t).pointAt s = ℓ.pointAt (addCoord t s) := by
  ext i
  simp only [pointAt, addPoint, addCoord, rebaseAt, smulPoint, mulCoord, decode_encodeScalar]
  rw [← encode_decodeScalar (ℓ.base i)]
  congr 1
  ring_nf
end
end MIPStarRE.LDT.DiagonalLine

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.DiagonalLine
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t s : Fq params) :
    rebaseAt (rebaseAt ℓ t) s = rebaseAt ℓ (addCoord t s) := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             (rebaseAt
               ({ base := base, direction := direction } : DiagonalLine params) t).pointAt s,
           direction := direction } : DiagonalLine params) =
        ({ base :=
             ({ base := base, direction := direction } : DiagonalLine params).pointAt
               (addCoord t s),
           direction := direction } : DiagonalLine params)
      exact congrArg
        (fun b => ({ base := b, direction := direction } : DiagonalLine params))
        (rebaseAt_pointAt { base := base, direction := direction } t s)
end MIPStarRE.LDT.DiagonalLine
