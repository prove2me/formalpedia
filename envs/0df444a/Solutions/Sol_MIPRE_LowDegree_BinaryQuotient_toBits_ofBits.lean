-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.toBits_ofBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:43:21.166176+00:00
-- url     : https://prove2.me/submissions/4e6cba0a-9ad8-46cc-8d50-08c69b6abebc

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotient.lean (solution of MIPRE.LowDegree.BinaryQuotient.toBits_ofBits);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
theorem _root_.solution (l : BitStr) (hlen : l.length = f.natDegree) :
    toBits f hf (ofBits f hf l) = l := by
  let b := AdjoinRoot.powerBasisAux' hf
  change (List.ofFn fun i : Fin f.natDegree =>
    coeffBit (b.repr (∑ j : Fin f.natDegree, (ofBool (l.getD j false) : ZMod 2) • b j) i)) = l
  have hc (i : Fin f.natDegree) :
      b.repr (∑ j : Fin f.natDegree, (ofBool (l.getD j false) : ZMod 2) • b j) i =
        ofBool (l.getD i false) := by
    simp [Finsupp.single_apply]
  simp only [hc, coeffBit_ofBool]
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
end MIPRE.LowDegree.BinaryQuotient
