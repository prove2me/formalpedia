-- Prove2me | solution 1 for MIPRE.Introspection.TypedEstimates.hiding_next_accepts_guarded
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:59:39.631797+00:00
-- url     : https://prove2.me/submissions/cdb55f7b-5c4a-434a-93f0-2cedfdb29d27

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HidingMaps.lean (solution of MIPRE.Introspection.TypedEstimates.hiding_next_accepts_guarded);
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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Theorems.Thm_MIPRE_Introspection_CLChecks_dualReadout_proj_compl_prefix
import Theorems.Thm_MIPRE_Introspection_CLChecks_outputPrefix_outputPrefix
import Theorems.Thm_MIPRE_Introspection_CLChecks_proj_outputPrefix_cons
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_hiding_next_accepts_conditional

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

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The register of the next stage is already fixed by the reported prefix. -/
theorem prefixRegister_outputPrefix_succ {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    prefixRegister P (k + 1) (P.outputPrefix k y) = prefixRegister P (k + 1) y := by
  induction P generalizing T k y with
  | zero => simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      obtain ⟨hfirst, hrest⟩ := proj_outputPrefix_cons hP k y
      simp only [prefixRegister]
      rw [hfirst, hrest, ih _ (hP.2 _) k _]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Longer claimed prefixes retain all the registers of shorter prefixes. -/
theorem prefixRegister_mono (P : CL.CLFun F ι ℓ) (y : ι → F)
    {k m : ℕ} (hkm : k ≤ m) : prefixRegister P k y ⊆ prefixRegister P m y := by
  induction P generalizing k m y with
  | zero => cases k <;> cases m <;> simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      cases m with
      | zero => omega
      | succ m =>
        exact union_subset_union (Subset.refl S) (ih _ _ (k := k) (m := m) (by omega))
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Equal preceding prefixes choose the same next register, including on
answers outside the image of the sampler. -/
theorem prefixRegister_congr {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) {y z : ι → F}
    (h : P.outputPrefix k y = P.outputPrefix k z) :
    prefixRegister P (k + 1) y = prefixRegister P (k + 1) z := by
  rw [← prefixRegister_outputPrefix_succ hP k y,
    ← prefixRegister_outputPrefix_succ hP k z, h]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Removing an earlier prefix does not change any later tail. -/
theorem tail_proj_tail (P : CL.CLFun F ι ℓ) (y x : ι → F)
    {k m : ℕ} (hkm : k ≤ m) :
    CL.proj (prefixRegister P m y)ᶜ (CL.proj (prefixRegister P k y)ᶜ x) =
      CL.proj (prefixRegister P m y)ᶜ x := by
  apply CL.proj_proj_of_subset
  exact compl_subset_compl.mpr (prefixRegister_mono P y hkm)
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.TypedEstimates
noncomputable section
open Finset Matrix Classical
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- On matching prefixes, the new keyed map factors through exactly the
previous hiding label; no raw discarded tail coordinates are needed. -/
theorem hidingNextGuarded_factor {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y yp x z : ι → F)
    (hmatch : P.outputPrefix k y = P.outputPrefix k z) :
    hidingNextGuarded P k (some z) (hidingCoarse P k (.hide y yp x :
      ParsedAnswer (ι → F) A PauliAnswer)) =
        hidingNextEarlier P k (some z) (.hide y yp x :
          ParsedAnswer (ι → F) A PauliAnswer) := by
  have hreg := CLChecks.prefixRegister_congr hP k hmatch
  simp only [hidingNextGuarded, hidingCoarse, hreg, if_pos hmatch,
    CLChecks.dualReadout_proj_compl_prefix hP, hidingNextEarlier, Option.map_some,
    CLChecks.tail_proj_tail P z x (show k + 1 ≤ k + 2 by omega)]
end
end MIPRE.Introspection.TypedEstimates

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem _root_.solution
    [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
    [Fintype F] [DecidableEq F] [Fintype A]
    (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.hide w k) (QuestionType.hide w j) a b = true) :
    hidingNextGuarded (L w) k.val (hidingNextLater (L w) k.val b).1
      (hidingCoarse (L w) k.val a) = (hidingNextLater (L w) k.val b).2 := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a with
  | pauli a => simp [TypedPredicate.fits] at hf
  | pair y a => simp [TypedPredicate.fits] at hf
  | read y yp a => simp [TypedPredicate.fits] at hf
  | hide y yp x =>
    cases b with
    | pauli b => simp [TypedPredicate.fits] at hf
    | pair z b => simp [TypedPredicate.fits] at hf
    | read z zp b => simp [TypedPredicate.fits] at hf
    | hide z zp t =>
      have hc := TypedPredicate.check_hiding_next L X Z projectPauli D DP w k j hk h
      have hmatch : (L w).outputPrefix k.val y =
          (L w).outputPrefix k.val ((L w).outputPrefix (k.val + 1) z) := by
        rw [CLChecks.outputPrefix_outputPrefix hL z (by omega)]
        exact hc.1
      change hidingNextGuarded (L w) k.val (some ((L w).outputPrefix (k.val + 1) z))
        (hidingCoarse (L w) k.val _) = _
      rw [hidingNextGuarded_factor hL k.val y yp x _ hmatch]
      exact hiding_next_accepts_conditional L X Z projectPauli D DP w k j hk hL h
end MIPRE.Introspection.TypedEstimates
