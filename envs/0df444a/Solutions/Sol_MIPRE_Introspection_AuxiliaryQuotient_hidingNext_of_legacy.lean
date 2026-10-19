-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryQuotient.hidingNext_of_legacy
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:55:44.645892+00:00
-- url     : https://prove2.me/submissions/8e209a19-4792-410b-b381-73434ce7c12c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryQuotientChecks.lean (solution of MIPRE.Introspection.AuxiliaryQuotient.hidingNext_of_legacy);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientChecks
import Theorems.Thm_MIPRE_Introspection_CLChecks_proj_outputPrefix_cons

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **A point differs from its canonical representative by an element of `S`.** For a line ---
`S = span {w}` --- this is the statement that the base point the seeded test reports lies on the
line through the sampled point, which is what lets a line answer be evaluated at the point. -/
theorem sub_canonLin_mem (S : Submodule F (Fin n → F)) (x : Fin n → F) :
    x - canonLin S x ∈ S :=
  Submodule.sub_projection_mem _ x
end
end MIPRE.CL

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem factorOfPrefix_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    P.factorOfPrefix k (P.outputPrefix k y) = P.factorOfPrefix k y := by
  induction P generalizing T k y with
  | zero => simp
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨ha, hb⟩ := proj_outputPrefix_cons hP k y
      simp only [CL.CLFun.factorOfPrefix_cons_succ]
      rw [ha, hb, ih _ (hP.2 _) k _]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem coordinateRestrict_proj {U V : Finset ι} (hUV : U ⊆ V) (x : ι → F) :
    coordinateRestrict U (CL.proj V x) = coordinateRestrict U x := by
  ext j
  exact if_pos (hUV ((Fintype.equivFin U).symm j).property)
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
/-- The recursive dual answer is exactly the selected coordinate linear
readout, transported back into the original register. -/
theorem dualReadout_stageLinear {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    dualReadout P k y x = coordinateInsert (P.factorOfPrefix k y)
      (CL.lperp (coordinateLinear (stageLinear P k y))
        (coordinateRestrict (P.factorOfPrefix k y) x)) := by
  induction P generalizing T k y x with
  | zero =>
    ext i
    simp [dualReadout, coordinateInsert]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih _ (hP.2 _) k _ x
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
set_option backward.isDefEq.respectTransparency false
variable {F : Type*} [Field F] {m n : ℕ}
/-- A linear map killing a subspace also kills the part removed by canonical
reduction. This permits changing quotient representatives without identifying
two coordinate enumerations. -/
theorem map_canonLin_of_le_ker {V : Type*} [AddCommGroup V] [Module F V]
    (S : Submodule F (Fin n → F)) (D : (Fin n → F) →ₗ[F] V)
    (hS : S ≤ D.ker) (x : Fin n → F) : D (CL.canonLin S x) = D x := by
  have h := hS (CL.sub_canonLin_mem S x)
  change D (x - CL.canonLin S x) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h.symm
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {S : Finset ι}
theorem registerDual_idempotent (L : CL.RegLinear F S) (x : ι → F) :
    registerDual L (registerDual L x) = registerDual L x := by
  simp only [registerDual, LinearMap.comp_apply, coordinateRestrict_insert]
  congr 1
  apply map_canonLin_of_le_ker
  rw [CL.ker_lperp]
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset CLChecks
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem registerDual_proj_input {S U : Finset (ι)} (L : CL.RegLinear F S)
    (hSU : S ⊆ U) (x : ι → F) : registerDual L (CL.proj U x) = registerDual L x := by
  simp only [registerDual, LinearMap.comp_apply, coordinateRestrict_proj hSU]
end
end MIPRE.Introspection.AuxiliaryDual

namespace MIPRE.Introspection.AuxiliaryDual
noncomputable section
open Finset CLChecks
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem stageDual_apply {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    stageDual P k y x = dualReadout P k y x := by
  rw [dualReadout_stageLinear hP]
  rfl
end
end MIPRE.Introspection.AuxiliaryDual

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryQuotient
open Finset CLChecks AuxiliaryDual
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem _root_.solution {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (k : ℕ) (u v : RegisterHideAnswer F ι)
    (h : CLChecks.hidingNext P k u v) : hidingNext P k u v := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  have hs : CL.proj (P.factorOfPrefix (k + 1) v.1) v.2.1 =
      stageDual P (k + 1) v.1 u.2.2 := by
    rw [stageDual_apply hP]
    simpa only [factorOfPrefix_outputPrefix hP] using h.2.2.2
  have hd := congrArg (stageDual P (k + 1) v.1) hs
  change registerDual (stageLinear P (k + 1) v.1)
    (CL.proj (P.factorOfPrefix (k + 1) v.1) v.2.1) =
    registerDual (stageLinear P (k + 1) v.1)
      (registerDual (stageLinear P (k + 1) v.1) u.2.2) at hd
  rw [registerDual_proj_input _ (Subset.refl _), registerDual_idempotent] at hd
  exact hd
end MIPRE.Introspection.AuxiliaryQuotient
