-- Prove2me | solution 1 for MIPRE.Weyl.proj_wX_binEquiv
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:42:58.79191+00:00
-- url     : https://prove2.me/submissions/5db66e6a-5ed5-466d-be11-9b2bdfb180a8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/WeylBinary.lean (solution of MIPRE.Weyl.proj_wX_binEquiv);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The defining Fourier average, as a rewrite. -/
theorem proj_def (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    proj w e = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a := rfl
end
end MIPRE.Weyl

namespace MIPRE.LowDegree
section
open Finset
variable {F K : Type*} [Field F] [Field K] [Algebra F K] {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
/-- **The coordinates of a self-dual basis are trace pairings** (`lem:downsize_field`, item 1):
`κ(x)ᵢ = tr(x eᵢ)`. -/
theorem coord_eq_trace {b : Module.Basis ι F K} (hb : IsSelfDualBasis b) (x : K) (i : ι) :
    b.repr x i = Algebra.trace F K (x * b i) := by
  conv_rhs => rw [← b.sum_repr x]
  rw [Finset.sum_mul, map_sum]
  have key : ∀ j : ι, Algebra.trace F K ((b.repr x j • b j) * b i)
      = if j = i then b.repr x j else 0 := by
    intro j
    rw [smul_mul_assoc, map_smul, hb j i, smul_eq_mul]
    split <;> simp
  rw [Finset.sum_congr rfl fun j _ => key j]
  simp
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
section
open Finset
variable {F K : Type*} [Field F] [Field K] [Algebra F K] {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
/-- **The trace form is the coordinate inner product** (`lem:downsize_field`, item 2):
`tr(xy) = κ(x) · κ(y)`. -/
theorem trace_mul_eq_dot {b : Module.Basis ι F K} (hb : IsSelfDualBasis b) (x y : K) :
    Algebra.trace F K (x * y) = ∑ i, b.repr x i * b.repr y i := by
  conv_lhs => rw [← b.sum_repr x]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm (b i) y, ← coord_eq_trace hb y i]
end
end MIPRE.LowDegree

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE MIPRE.LowDegree
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {b : Module.Basis ι (ZMod 2) F}
theorem binEquiv_add (a a' : n → F) :
    binEquiv (n := n) b (a + a') = binEquiv b a + binEquiv b a' := by
  funext p
  simp [Pi.add_apply]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE MIPRE.LowDegree
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {b : Module.Basis ι (ZMod 2) F}
theorem binEquiv_eq_iff (a a' : n → F) :
    binEquiv (n := n) b a = binEquiv b a' ↔ a = a' :=
  (binEquiv b).apply_eq_iff_eq
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE MIPRE.LowDegree
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {b : Module.Basis ι (ZMod 2) F}
/-- **Self-duality is exactly what makes the form transport.** -/
theorem trDot_binEquiv (hb : IsSelfDualBasis b) (a a' : n → F) :
    trDot (binEquiv (n := n) b a) (binEquiv b a') = trDot a a' := by
  rw [trDot, trDot, Algebra.trace_self_apply, Fintype.sum_prod_type, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [trace_mul_eq_dot hb]
  rfl
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE MIPRE.LowDegree
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {b : Module.Basis ι (ZMod 2) F}
/-- **The `X`-type family transports**, and needs no self-duality: the relabelling is additive,
which is all a shift knows about. -/
theorem wX_binEquiv (a : n → F) :
    (wX (binEquiv (n := n) b a)).submatrix (binEquiv b) (binEquiv b) = wX a := by
  ext j i
  rw [Matrix.submatrix_apply, wX_apply, wX_apply]
  by_cases h : j = i + a
  · rw [if_pos h, if_pos (by rw [h, binEquiv_add])]
  · rw [if_neg h, if_neg ?_]
    intro hh
    exact h (binEquiv_eq_iff (b := b) j (i + a) |>.mp (by rw [hh, binEquiv_add]))
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE MIPRE.LowDegree
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {b : Module.Basis ι (ZMod 2) F}
theorem card_binEquiv (b : Module.Basis ι (ZMod 2) F) :
    Fintype.card (n × ι → ZMod 2) = Fintype.card (n → F) :=
  (Fintype.card_congr (binEquiv (n := n) b)).symm
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE MIPRE.LowDegree
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {b : Module.Basis ι (ZMod 2) F}
/-- **The Fourier average commutes with the relabelling**, for an arbitrary family: no group law
and no self-duality beyond the form's. -/
theorem proj_binEquiv (hb : IsSelfDualBasis b)
    (w : (n × ι → ZMod 2) → Matrix (n × ι → ZMod 2) (n × ι → ZMod 2) ℂ) (e : n → F) :
    (proj w (binEquiv b e)).submatrix (binEquiv b) (binEquiv b)
      = proj (fun a => (w (binEquiv (n := n) b a)).submatrix (binEquiv b) (binEquiv b)) e := by
  ext j i
  rw [Matrix.submatrix_apply, proj_def, proj_def, card_binEquiv (n := n) b]
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply, smul_eq_mul]
  congr 1
  refine Fintype.sum_equiv (binEquiv (n := n) b).symm _ _ fun x => ?_
  rw [← trDot_binEquiv hb ((binEquiv (n := n) b).symm x) e, Equiv.apply_symm_apply]
end
end MIPRE.Weyl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix MIPRE MIPRE.LowDegree
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {b : Module.Basis ι (ZMod 2) F}
theorem _root_.solution (hb : IsSelfDualBasis b) (e : n → F) :
    (proj wX (binEquiv (n := n) b e)).submatrix (binEquiv b) (binEquiv b)
      = proj (wX (F := F) (n := n)) e := by
  rw [proj_binEquiv hb]
  congr 1
  exact funext fun a => wX_binEquiv a
end MIPRE.Weyl
