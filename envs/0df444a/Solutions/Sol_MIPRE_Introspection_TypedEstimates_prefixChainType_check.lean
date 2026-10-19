-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.prefixChainType_check
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:22:55.694982+00:00
-- url     : https://prove2.me/submissions/567d2809-ec7c-4b16-ba41-56c5aa7b4434

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypedPrefixChain.lean (solution of MIPRE.Introspection.TypedEstimates.prefixChainType_check);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
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
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Theorems.Thm_MIPRE_Introspection_CLChecks_outputPrefix_outputPrefix

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.TypedPredicate
noncomputable section
open Classical
variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- Accepted answers have the correct constructors on both sides. -/
theorem check_formats {t u : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t u a b = true) : fits t a = true ∧ fits u b = true := by
  simp only [check, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2⟩
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypedPredicate
noncomputable section
open Classical
variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- Acceptance includes the auxiliary check in the displayed player order. -/
theorem check_directed {t u : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t u a b = true) :
    directed L X Z projectPauli D t u a b = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.1.2
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypedPredicate
noncomputable section
open Classical
variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- Acceptance also includes the auxiliary check with the players reversed. -/
theorem check_directed_reversed {t u : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t u a b = true) :
    directed L X Z projectPauli D u t b a = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.2
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypedPredicate
noncomputable section
open Classical
variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- The last hiding level and Read have the tested common prefix and full dual answer. -/
theorem check_hiding_read (w : Bool) (k : Fin ℓ) (hk : k.val + 1 = ℓ)
    {y yp x z zp : ι → F} {a : A}
    (h : check L X Z projectPauli D DP (.inr (.hide k, w)) (.inr (.read, w))
      (.hide y yp x) (.read z zp a) = true) :
    CLChecks.hidingRead (L w) (y, yp, x) (z, zp, a) := by
  have hd := check_directed L X Z projectPauli D DP h
  simp only [directed, hk, and_self, ↓reduceIte] at hd
  exact @of_decide_eq_true _ (Classical.propDecidable _) hd
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypedPredicate
noncomputable section
open Classical
variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- Accepted consecutive hiding answers satisfy all four source comparisons. -/
theorem check_hiding_next (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    {y yp x z zp t : ι → F}
    (h : check L X Z projectPauli D DP (.inr (.hide k, w)) (.inr (.hide j, w))
      (.hide y yp x) (.hide z zp t) = true) :
    CLChecks.hidingNext (L w) k.val (y, yp, x) (z, zp, t) := by
  have hd := check_directed L X Z projectPauli D DP h
  simp only [directed, hk, and_self, ↓reduceIte] at hd
  exact @of_decide_eq_true _ (Classical.propDecidable _) hd
end
end MIPRE.Introspection.TypedPredicate

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- Every prefix already present at the earlier hiding level agrees on an
accepted adjacent hiding edge, including arbitrary off-image claimed outputs. -/
theorem check_hiding_next_prefix (w : Bool) (hL : (L w).SupportedOn univ)
    (k j : Fin ℓ) (hk : k.val + 1 = j.val) (m : ℕ) (hm : m ≤ k.val)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.hide w k) (QuestionType.hide w j) a b = true) :
    reportedPrefix (L w) m (.hide k) a = reportedPrefix (L w) m (.hide j) b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y yp x z zp t
  have hp := (TypedPredicate.check_hiding_next L X Z projectPauli D DP w k j hk h).1
  have he := congrArg ((L w).outputPrefix m) hp
  simp only [CLChecks.outputPrefix_outputPrefix hL _ hm] at he
  exact congrArg some he
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- The last hiding/Read test preserves every question prefix available at
the last hiding level. -/
theorem check_hiding_read_prefix (w : Bool) (hL : (L w).SupportedOn univ)
    (k : Fin ℓ) (hk : k.val + 1 = ℓ) (m : ℕ) (hm : m ≤ k.val)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.hide w k) (QuestionType.read w) a b = true) :
    reportedPrefix (L w) m (.hide k) a = reportedPrefix (L w) m .read b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y yp x z zp b
  have hp := (TypedPredicate.check_hiding_read L X Z projectPauli D DP w k hk h).1
  have he := congrArg ((L w).outputPrefix m) hp
  have hm' : m ≤ ℓ - 1 := by omega
  simp only [CLChecks.outputPrefix_outputPrefix hL _ hm'] at he
  exact congrArg some he
end
end MIPRE.Introspection.TypedEstimates

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
/-- Read and Introspect preserve every question prefix in this orientation. -/
theorem check_read_introspect_prefix (w : Bool) (m : ℕ)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.read w) (QuestionType.introspect w) a b = true) :
    reportedPrefix (L w) m .read a = reportedPrefix (L w) m .introspect b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i y yp a z b
  have hd := TypedPredicate.check_directed_reversed L X Z projectPauli D DP h
  simp only [TypedPredicate.directed, ↓reduceIte] at hd
  have he : z = y ∧ b = a := @of_decide_eq_true _ (Classical.propDecidable _) hd
  exact congrArg (fun y => some ((L w).outputPrefix m y)) he.1.symm
end
end MIPRE.Introspection.TypedEstimates

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
variable [DecidableEq PauliType]
theorem _root_.solution (w : Bool) (hL : (L w).SupportedOn univ)
    (j : Fin ℓ) (m : ℕ) (hm : m ≤ j.val) (i : ℕ) (hi : i < ℓ - j.val + 1)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (.inr (prefixChainType j i, w)) (.inr (prefixChainType j (i + 1), w)) a b = true) :
    reportedPrefix (L w) m (prefixChainType j i) a =
      reportedPrefix (L w) m (prefixChainType j (i + 1)) b := by
  by_cases hs : j.val + (i + 1) < ℓ
  · have hp : j.val + i < ℓ := by omega
    simp only [prefixChainType, dif_pos hs, dif_pos hp] at h ⊢
    exact check_hiding_next_prefix L X Z projectPauli D DP w hL _ _
      (by simp; omega) m (by simp; omega) h
  · by_cases hp : j.val + i < ℓ
    · have he : j.val + (i + 1) = ℓ := by omega
      simp only [prefixChainType, dif_neg hs, dif_pos hp, if_pos he] at h ⊢
      exact check_hiding_read_prefix L X Z projectPauli D DP w hL _
        (by simp; omega) m (by simp; omega) h
    · have he : j.val + i = ℓ := by omega
      have hn : j.val + (i + 1) ≠ ℓ := by omega
      simp only [prefixChainType, dif_neg hs, dif_neg hp, if_pos he, if_neg hn] at h ⊢
      exact check_read_introspect_prefix L X Z projectPauli D DP w m h
end MIPRE.Introspection.TypedEstimates
