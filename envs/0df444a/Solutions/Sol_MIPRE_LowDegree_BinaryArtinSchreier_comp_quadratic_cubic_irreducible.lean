-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryArtinSchreier.comp_quadratic_cubic_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:17.133729+00:00
-- url     : https://prove2.me/submissions/21c428cc-8c4e-40f1-a063-8ffeb320a8ae

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean (solution of MIPRE.LowDegree.BinaryArtinSchreier.comp_quadratic_cubic_irreducible);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Theorems.Thm_MIPRE_LowDegree_BinaryArtinSchreier_next_quadratic_irreducible

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryArtinSchreier
noncomputable section
open Polynomial Module
variable {K : Type*} [Field K]
variable [CharP K 2]
/-- The multiplicative next parameter is the uniform cubic expression in the new root. -/
theorem next_parameter_eq_cubic (a : K) (ha : Irreducible (quadratic a)) :
    let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
    algebraMap K (AdjoinRoot (quadratic a)) a * AdjoinRoot.root (quadratic a) =
      AdjoinRoot.root (quadratic a) ^ 3 + AdjoinRoot.root (quadratic a) ^ 2 := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  let : CharP (AdjoinRoot (quadratic a)) 2 := charP_of_injective_algebraMap'
    K (A := AdjoinRoot (quadratic a)) 2
  rw [← CharTwo.add_eq_zero.mp (root_relation a)]
  ring
end
end MIPRE.LowDegree.BinaryArtinSchreier

namespace MIPRE.LowDegree.BinaryArtinSchreier
noncomputable section
open Polynomial Module
variable {K : Type*} [Field K]
variable [CharP K 2]
/-- The source's cubic expression therefore preserves the no-root invariant. -/
theorem cubic_quadratic_irreducible (a : K) (ha : Irreducible (quadratic a)) :
    let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
    Irreducible (quadratic
      (AdjoinRoot.root (quadratic a) ^ 3 + AdjoinRoot.root (quadratic a) ^ 2)) := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  rw [← next_parameter_eq_cubic a ha]
  exact next_quadratic_irreducible a ha
end
end MIPRE.LowDegree.BinaryArtinSchreier

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryArtinSchreier
open Polynomial Module
variable {K : Type*} [Field K]
variable [CharP K 2]
theorem _root_.solution [Finite K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] (t : ℕ)
    (hK : Module.finrank (ZMod 2) K = 2 ^ t)
    (a : K) (ha : Irreducible (quadratic a))
    (g : (ZMod 2)[X]) (hg : g.Monic) (hd : g.natDegree = 2 ^ t)
    (hz : aeval a g = 0) :
    let : Fact (Irreducible (g.comp (quadratic (0 : ZMod 2)))) :=
      ⟨comp_quadratic_irreducible t hK a ha g hg hd hz⟩
    Irreducible (quadratic
      (AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2))) ^ 3 +
        AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2))) ^ 2)) := by
  let : Fact (Irreducible (g.comp (quadratic (0 : ZMod 2)))) :=
    ⟨comp_quadratic_irreducible t hK a ha g hg hd hz⟩
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  let : CharP (AdjoinRoot (quadratic a)) 2 := charP_of_injective_algebraMap'
    K (A := AdjoinRoot (quadratic a)) 2
  have hp : aeval (AdjoinRoot.root (quadratic a)) (g.comp (quadratic (0 : ZMod 2))) = 0 := by
    rw [aeval_comp]
    have hroot : aeval (AdjoinRoot.root (quadratic a)) (quadratic (0 : ZMod 2)) =
        algebraMap K (AdjoinRoot (quadratic a)) a := by
      change aeval (AdjoinRoot.root (quadratic a)) (X ^ 2 + X + C (0 : ZMod 2)) = _
      rw [map_add, map_add, map_pow, aeval_X, aeval_C, map_zero, add_zero]
      exact CharTwo.add_eq_zero.mp (root_relation a)
    rw [hroot]
    change aeval ((IsScalarTower.toAlgHom (ZMod 2) K (AdjoinRoot (quadratic a))) a) g = 0
    rw [aeval_algHom_apply, hz, map_zero]
  let φ := AdjoinRoot.liftAlgHom (g.comp (quadratic (0 : ZMod 2)))
    (Algebra.ofId (ZMod 2) (AdjoinRoot (quadratic a))) (AdjoinRoot.root (quadratic a)) hp
  have hφ : φ (AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2)))) =
      AdjoinRoot.root (quadratic a) := AdjoinRoot.liftAlgHom_root _ _ _ _
  apply (quadratic_irreducible_iff _).2
  intro x hx
  have hx' := congrArg φ hx
  simp only [map_add, map_pow, map_zero, hφ] at hx'
  exact (quadratic_irreducible_iff _).1 (cubic_quadratic_irreducible a ha) (φ x) hx'
end MIPRE.LowDegree.BinaryArtinSchreier
