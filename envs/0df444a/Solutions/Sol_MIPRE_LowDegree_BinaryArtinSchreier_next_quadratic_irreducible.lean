-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryArtinSchreier.next_quadratic_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:43:19.495685+00:00
-- url     : https://prove2.me/submissions/d05e1f4d-153f-4586-a3b9-3d32221a7616

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean (solution of MIPRE.LowDegree.BinaryArtinSchreier.next_quadratic_irreducible);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryArtinSchreier
noncomputable section
open Polynomial Module
variable {K : Type*} [Field K]
/-- Each element has its two coefficients in the specified quadratic power basis. -/
theorem exists_coordinates (a : K) (x : AdjoinRoot (quadratic a)) :
    ∃ u v : K, x = algebraMap K _ u + algebraMap K _ v * AdjoinRoot.root (quadratic a) := by
  refine ⟨(quadraticBasis a).repr x 0, (quadraticBasis a).repr x 1, ?_⟩
  have h := (quadraticBasis a).sum_repr x
  simpa only [Fin.sum_univ_two, quadraticBasis_apply, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, Algebra.smul_def, mul_one] using h.symm
end
end MIPRE.LowDegree.BinaryArtinSchreier

namespace MIPRE.LowDegree.BinaryArtinSchreier
noncomputable section
open Polynomial Module
variable {K : Type*} [Field K]
/-- The coefficient of the root in a zero linear combination is zero. -/
theorem linear_coeff_eq_zero (a u v : K)
    (h : algebraMap K (AdjoinRoot (quadratic a)) u +
      algebraMap K _ v * AdjoinRoot.root (quadratic a) = 0) : v = 0 := by
  have h' : u • quadraticBasis a 0 + v • quadraticBasis a 1 = 0 := by
    simpa only [quadraticBasis_apply, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      Algebra.smul_def, mul_one] using h
  have hc := congrArg (fun x => (quadraticBasis a).repr x 1) h'
  simpa only [map_add, map_smul, Basis.repr_self, map_zero, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Fin.zero_ne_one,
    if_false, if_true, mul_zero, zero_add, mul_one, Finsupp.zero_apply] using hc
end
end MIPRE.LowDegree.BinaryArtinSchreier

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryArtinSchreier
open Polynomial Module
variable {K : Type*} [Field K]
variable [CharP K 2]
theorem _root_.solution (a : K) (ha : Irreducible (quadratic a)) :
    let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
    Irreducible (quadratic
      (algebraMap K (AdjoinRoot (quadratic a)) a * AdjoinRoot.root (quadratic a))) := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  let : CharP (AdjoinRoot (quadratic a)) 2 := charP_of_injective_algebraMap'
    K (A := AdjoinRoot (quadratic a)) 2
  apply (quadratic_irreducible_iff _).2
  intro x hx
  obtain ⟨u, v, rfl⟩ := exists_coordinates a x
  have hr := root_relation a
  have hz :
      algebraMap K (AdjoinRoot (quadratic a)) (u ^ 2 + u + v ^ 2 * a) +
        algebraMap K _ (v ^ 2 + v + a) * AdjoinRoot.root (quadratic a) = 0 := by
    simp only [map_add, map_mul, map_pow]
    linear_combination (norm := skip) hx - (algebraMap K (AdjoinRoot (quadratic a)) v) ^ 2 * hr
    ring_nf
    simp [CharTwo.two_eq_zero]
  exact (quadratic_irreducible_iff a).1 ha v (linear_coeff_eq_zero a _ _ hz)
end MIPRE.LowDegree.BinaryArtinSchreier
