-- Prove2me | solution 1 for MIPRE.QLD.PauliCL.ExplicitSeed.binaryOutputPermutation_presentation
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:18:05.0727+00:00
-- url     : https://prove2.me/submissions/a238b375-3bc9-4c5b-b19e-bd9dd049168e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/CLExplicitTransport.lean (solution of MIPRE.QLD.PauliCL.ExplicitSeed.binaryOutputPermutation_presentation);
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
import Definitions.Def_MIPRE_Background_QLD_CLExplicitTransport
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
theorem compl_product_univ (S : Finset ι) :
    (S ×ˢ (Finset.univ : Finset κ))ᶜ = Sᶜ ×ˢ Finset.univ := by
  ext ⟨i, j⟩; simp
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
/-- `L^↓ = ↓ ∘ L ∘ ↓⁻¹`. -/
theorem eval_downsize (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.downsize b).eval (downsizeEquiv b x) = downsizeEquiv b (P.eval x) := by
  induction P generalizing x with
  | zero => simp
  | cons S L₁ next ih =>
    rw [downsize_cons, eval_cons, eval_cons, RegLinear.downsize_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, compl_product_univ,
      ← downsizeEquiv_proj, ih, map_add]
end
end MIPRE.CL.CLFun

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t : ℕ} [NeZero m]
/-- Evaluation agrees with the actual field presentation under the binary
coordinate equivalence. -/
theorem binaryPresentation_eval (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (x : Coord m → F) :
    (binaryPresentation hm b T).eval (binaryVectorEquiv b x) =
      binaryVectorEquiv b ((presentation hm T).eval x) := by
  change (((presentation hm T).downsize b).reindex (binaryCoordEquiv m t)).eval
    (CL.reindexEquiv (binaryCoordEquiv m t) (CL.downsizeEquiv b x)) = _
  rw [CL.CLFun.eval_reindex, CL.CLFun.eval_downsize]
  rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL.ExplicitSeed
noncomputable section
open Finset Classical
open MIPRE.Introspection.SeedProgram
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
variable [Algebra (ZMod 2) F] {t : ℕ}
theorem binaryPresentation_eval (χ : F → Fin m)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (x : Coord m → F) :
    (binaryPresentation χ b T).eval (binaryVectorEquiv b x) =
      binaryVectorEquiv b ((presentation χ T).eval x) := by
  change (((presentation χ T).downsize b).reindex (binaryCoordEquiv m t)).eval
    (CL.reindexEquiv (binaryCoordEquiv m t) (CL.downsizeEquiv b x)) = _
  rw [CL.CLFun.eval_reindex, CL.CLFun.eval_downsize]
  rfl
end
end MIPRE.QLD.PauliCL.ExplicitSeed

namespace MIPRE.QLD.PauliCL.ExplicitSeed
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
theorem vectorPermutation_content (π : F ≃ F) (c : Content F m) :
    vectorPermutation π (contentVector c) = contentVector (contentPermutation π c) := by
  change contentEquiv (contentPermutation π (contentEquiv.symm (contentEquiv c))) = _
  rw [Equiv.symm_apply_apply]
  rfl
end
end MIPRE.QLD.PauliCL.ExplicitSeed

namespace MIPRE.QLD.PauliCL.ExplicitSeed
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem outputPermutation_presentation (hm : m ∣ Fintype.card F)
    (χ : F → Fin m) (π : F ≃ F) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (T : Ty) (c : Content F m) :
    outputPermutation π T ((presentation χ T).eval (contentVector c)) =
      (PauliCL.presentation hm T).eval (contentVector (contentPermutation π c)) := by
  cases T <;> (try cases ‹Bas›) <;>
    simp +instances only [outputPermutation, vectorPermutation, contentEquiv, contentPermutation,
      presentation, PauliCL.presentation, seedMap, secondMap, PauliCL.secondMap,
      finalMap, PauliCL.finalMap, CL.CLFun.eval, CL.RegLinear.zero_apply,
      CL.RegLinear.id_apply, pointMap_apply, directionMap_apply, Pi.add_apply, Pi.zero_apply,
      Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.coe_fn_mk, vectorContent]
  all_goals
    funext i
    cases i <;> (try cases ‹Bas›) <;>
      simp +instances only [CL.RegLinear.instFunLikeForall, contentVector, vectorContent,
        pointMap, directionMap, Pi.add_apply, Pi.zero_apply, LinearMap.id_apply] <;>
      simp +instances [CL.proj_apply, seedSet, directionSet, finalSet, contentVector, vectorContent,
        pointMap, directionMap, hχ]
end
end MIPRE.QLD.PauliCL.ExplicitSeed

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.PauliCL.ExplicitSeed
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
variable [Algebra (ZMod 2) F] {t : ℕ}
theorem _root_.solution (hm : m ∣ Fintype.card F)
    (χ : F → Fin m) (π : F ≃ F) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    binaryOutputPermutation π b T ((binaryPresentation χ b T).eval x) =
      (PauliCL.binaryPresentation hm b T).eval (binarySeedPermutation π b x) := by
  obtain ⟨v, rfl⟩ := (binaryVectorEquiv (m := m) b).surjective x
  obtain ⟨c, rfl⟩ := (contentEquiv (F := F) (m := m)).surjective v
  rw [binaryPresentation_eval]
  change binaryVectorEquiv b (outputPermutation π T
    ((binaryVectorEquiv b).symm (binaryVectorEquiv b
      ((presentation χ T).eval (contentVector c))))) =
    (PauliCL.binaryPresentation hm b T).eval
      (binaryVectorEquiv b (vectorPermutation π
        ((binaryVectorEquiv b).symm (binaryVectorEquiv b (contentVector c)))))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    vectorPermutation_content, PauliCL.binaryPresentation_eval,
    outputPermutation_presentation hm χ π hχ]
end MIPRE.QLD.PauliCL.ExplicitSeed
