-- Prove2me | solution 1 for MIPRE.SAT.PcpAlgebra.literal_product_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:58.280165+00:00
-- url     : https://prove2.me/submissions/cb5df9fa-4098-4195-837c-c4b3e2780126

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpBlocks.lean (solution of MIPRE.SAT.PcpAlgebra.literal_product_degree_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.PcpParams
noncomputable section
open Finset MvPolynomial LowDegree
theorem blockIndex_injective (P : PcpParams) (i : Fin 5) :
    Function.Injective (P.blockIndex i) := by
  intro j k h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [blockIndex] at this
  omega
end
end MIPRE.SAT.PcpParams

namespace MIPRE.SAT.PcpParams
noncomputable section
open Finset MvPolynomial LowDegree
theorem blockIndex_eq_imp (P : PcpParams) (i t : Fin 5) (j k : Fin P.m)
    (h : P.blockIndex i j = P.blockIndex t k) : i = t := by
  have hj : j.val < P.m := j.isLt
  have hk : k.val < P.m := k.isLt
  have hv := congrArg Fin.val h
  simp only [blockIndex] at hv
  have hm : j.val = k.val := by
    have := congrArg (fun n => n % P.m) hv
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] using this
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < P.m) (by omega)
end
end MIPRE.SAT.PcpParams

namespace MIPRE.SAT.PcpParams
noncomputable section
open Finset MvPolynomial LowDegree
theorem signIndex_injective (P : PcpParams) : Function.Injective P.signIndex := by
  intro i t h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [signIndex] at this
  omega
end
end MIPRE.SAT.PcpParams

namespace MIPRE.SAT.PcpParams
noncomputable section
open Finset MvPolynomial LowDegree
theorem blockIndex_ne_signIndex (P : PcpParams) (i t : Fin 5) (j : Fin P.m) :
    P.blockIndex i j ≠ P.signIndex t := by
  intro h
  have hi := Nat.mul_le_mul_right P.m (Nat.lt_succ_iff.mp i.isLt)
  have hj := j.isLt
  have := congrArg Fin.val h
  simp only [blockIndex, signIndex] at this
  omega
end
end MIPRE.SAT.PcpParams

namespace MIPRE.SAT.PcpAlgebra
noncomputable section
open Finset MvPolynomial LowDegree
variable {P : PcpParams} {F : Type*} [Field F]
theorem degreeOf_liftAnswer_le (i : Fin 5) (g : MvPolynomial (Fin P.m) F)
    {d : ℕ} (hg : ∀ j, g.degreeOf j ≤ d) (j : Fin P.m') :
    (liftAnswer i g).degreeOf j ≤ d := by
  by_cases h : ∃ k, P.blockIndex i k = j
  · obtain ⟨k, rfl⟩ := h
    rw [liftAnswer, degreeOf_rename_of_injective (P.blockIndex_injective i)]
    exact hg k
  · have hz : (liftAnswer i g).degreeOf j = 0 := by
      by_contra hn
      obtain ⟨k, _, hk⟩ := mem_vars_rename _ g (mem_vars_iff_degreeOf_ne_zero.mpr hn)
      exact h ⟨k, hk⟩
    rw [hz]
    exact Nat.zero_le _
end
end MIPRE.SAT.PcpAlgebra

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.PcpAlgebra
open Finset MvPolynomial LowDegree
variable {P : PcpParams} {F : Type*} [Field F]
theorem _root_.solution (g : Fin 5 → MvPolynomial (Fin P.m) F)
    (hg : ∀ i j, (g i).degreeOf j ≤ 1) (j : Fin P.m') :
    (∏ i, (liftAnswer i (g i) - X (P.signIndex i))).degreeOf j ≤ 1 := by
  let f : Fin 5 → MvPolynomial (Fin P.m') F := fun i =>
    liftAnswer i (g i) - X (P.signIndex i)
  have hbound (i : Fin 5) : (f i).degreeOf j ≤ 1 := by
    apply (degreeOf_sub_le j _ _).trans
    apply max_le (degreeOf_liftAnswer_le i (g i) (hg i) j)
    by_cases h : j = P.signIndex i
    · simp [h]
    · simp [degreeOf_X_of_ne h]
  have hunique (i t : Fin 5) (hi : 0 < (f i).degreeOf j)
      (ht : 0 < (f t).degreeOf j) : i = t := by
    rcases factor_degree_pos i (g i) j hi with ⟨a, ha⟩ | ha
    · rcases factor_degree_pos t (g t) j ht with ⟨b, hb⟩ | hb
      · exact P.blockIndex_eq_imp i t a b (ha.trans hb.symm)
      · exact (P.blockIndex_ne_signIndex i t a (ha.trans hb.symm)).elim
    · rcases factor_degree_pos t (g t) j ht with ⟨b, hb⟩ | hb
      · exact (P.blockIndex_ne_signIndex t i b (hb.trans ha.symm)).elim
      · exact P.signIndex_injective (ha.trans hb.symm)
  apply (degreeOf_prod_le j univ f).trans
  by_cases h : ∃ i, 0 < (f i).degreeOf j
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · exact hbound i
    · intro t _ hti
      by_contra ht
      exact hti (hunique t i (Nat.pos_of_ne_zero ht) hi)
    · simp
  · push Not at h
    simp only [Nat.le_zero] at h
    simp [h]
end MIPRE.SAT.PcpAlgebra
