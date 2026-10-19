-- Prove2me | solution 1 for MIPRE.QLD.PauliCL.ExplicitSeed.binaryPresentation_exactlyOn
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:18:01.504992+00:00
-- url     : https://prove2.me/submissions/a0efce77-f643-4f63-bde8-ff33e1938654

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/CLExplicitSeed.lean (solution of MIPRE.QLD.PauliCL.ExplicitSeed.binaryPresentation_exactlyOn);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
theorem sdiff_product_univ (S T : Finset ι) :
    (T ×ˢ (Finset.univ : Finset κ)) \ (S ×ˢ Finset.univ) = (T \ S) ×ˢ Finset.univ := by
  ext ⟨i, j⟩; simp
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
theorem ExactlyOn.downsize (b : Module.Basis κ K F) {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.ExactlyOn T) : (P.downsize b).ExactlyOn (T ×ˢ Finset.univ) := by
  induction P generalizing T with
  | zero =>
    have hT : T = ∅ := hP
    show T ×ˢ Finset.univ = ∅
    rw [hT, Finset.empty_product]
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    refine ⟨Finset.product_subset_product hS (Finset.Subset.refl _), fun v => ?_⟩
    rw [sdiff_product_univ]
    exact ih _ (hnext _)
end
end MIPRE.CL.CLFun

namespace MIPRE.CL
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
theorem map_sdiff' (e : ι ≃ ι') (S T : Finset ι) :
    T.map e.toEmbedding \ S.map e.toEmbedding = (T \ S).map e.toEmbedding := by
  ext i; simp [Finset.mem_map_equiv]
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
variable {ℓ : ℕ}
theorem ExactlyOn.reindex (e : ι ≃ ι') {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    (P.reindex e).ExactlyOn (T.map e.toEmbedding) := by
  induction P generalizing T with
  | zero =>
    have hT : T = ∅ := hP
    show T.map e.toEmbedding = ∅
    rw [hT, Finset.map_empty]
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    refine ⟨Finset.map_subset_map.mpr hS, fun v => ?_⟩
    rw [map_sdiff']
    exact ih _ (hnext _)
end
end MIPRE.CL.CLFun

namespace MIPRE.QLD.PauliCL.ExplicitSeed
noncomputable section
open Finset Classical
open MIPRE.Introspection.SeedProgram
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
theorem presentation_exactlyOn (χ : F → Fin m) (t : Ty) :
    (presentation χ t).ExactlyOn univ := by
  refine ⟨subset_univ _, fun _ => ⟨?_, fun _ => ?_⟩⟩
  · intro c hc
    cases c <;> simp_all [seedSet, directionSet]
  · have he : (univ \ seedSet m) \ directionSet m = finalSet m := by
      ext c
      simp [finalSet]
    rw [he]
    exact ⟨Subset.rfl, fun _ => by simp⟩
end
end MIPRE.QLD.PauliCL.ExplicitSeed

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.PauliCL.ExplicitSeed
open Finset Classical
open MIPRE.Introspection.SeedProgram
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
variable [Algebra (ZMod 2) F] {t : ℕ}
theorem _root_.solution (χ : F → Fin m)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) :
    (binaryPresentation χ b T).ExactlyOn univ := by
  have h := ((presentation_exactlyOn χ T).downsize b).reindex (binaryCoordEquiv m t)
  simpa only [binaryPresentation, Finset.univ_product_univ, Finset.map_univ_equiv] using h
end MIPRE.QLD.PauliCL.ExplicitSeed
