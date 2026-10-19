-- Prove2me | solution 1 for MIPRE.Introspection.Honest.hideOp_conditionalIdeal_eq_next
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:49:44.702229+00:00
-- url     : https://prove2.me/submissions/6e9bc93e-05ab-497b-a536-3384e5f5029b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ConditionalNormalizerIdeal.lean (solution of MIPRE.Introspection.Honest.hideOp_conditionalIdeal_eq_next);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Theorems.Thm_MIPRE_Introspection_CLChecks_dualReadout_proj_compl_prefix
import Theorems.Thm_MIPRE_Introspection_CLChecks_outputPrefix_outputPrefix
import Theorems.Thm_MIPRE_Introspection_CLChecks_proj_outputPrefix_cons
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_accepts_next
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_commute_next
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_entry_nonzero
import Theorems.Thm_MIPRE_Introspection_Honest_hideRegister_marginal
import Theorems.Thm_MIPRE_Introspection_conditionalIdeal_eq_coarse_of_reject
import Theorems.Thm_MIPRE_Introspection_linear_measurement_isPVM
import Theorems.Thm_MIPRE_Introspection_linear_measurements_commute
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj
import Theorems.Thm_MIPRE_Weyl_sum_proj
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_star_sgn
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_proj_of_disjoint {S T : Finset ι} (h : Disjoint S T) (x : ι → F) :
    proj S (proj T x) = 0 := by
  rw [proj_proj, Finset.disjoint_iff_inter_eq_empty.mp h, proj_empty]
end
end MIPRE.CL

namespace MIPRE.CL.RegLinear
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
variable {S T : Finset ι}
theorem proj_apply_of_disjoint (L : RegLinear F S) (h : Disjoint T S) (x : ι → F) :
    proj T (L x) = 0 := by
  rw [← L.proj_apply x, proj_proj_of_disjoint h]
end
end MIPRE.CL.RegLinear

namespace MIPRE.CL.RegLinear
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
variable {S T : Finset ι}
theorem proj_compl_apply [Fintype ι] (L : RegLinear F S) (x : ι → F) : proj Sᶜ (L x) = 0 :=
  L.proj_apply_of_disjoint disjoint_compl_left x
end
end MIPRE.CL.RegLinear

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_comm (x y : Fin n → F) : dotForm F n x y = dotForm F n y x := by
  simp only [dotForm_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_isRefl : (dotForm F n).IsRefl := fun x y h => by
  rw [dotForm_comm]; exact h
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_nondegenerate : (dotForm F n).Nondegenerate := by
  have key : ∀ x : Fin n → F, ∀ i : Fin n,
      dotForm F n x (Pi.single i 1) = x i := by
    intro x i
    rw [dotForm_apply, Finset.sum_eq_single i
      (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ i) h)]
    simp
  refine ⟨fun x hx => funext fun i => ?_, fun y hy => funext fun i => ?_⟩
  · rw [← key x i]; exact hx _
  · rw [← key y i, dotForm_comm]; exact hy _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **`lem:perp_perp`**, second part: the dot-product perp is an involution on subspaces, over
every field. -/
theorem perp_perp (S : Submodule F (Fin n → F)) : perp (perp S) = S :=
  LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl S
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem SupportedOn.lift {P : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (h : T' ⊆ T) : (P.lift T').SupportedOn T := by
  induction P generalizing T T' with
  | zero => exact ⟨h, fun _ => trivial⟩
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    exact ⟨hS, fun v => ih v (hnext v) (Finset.sdiff_subset_sdiff h (Finset.Subset.refl S))⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
/-- Item (1) of `lem:cl-kth`: the `k`-th marginal is a `k`-level CL function on the same space. -/
theorem SupportedOn.truncate {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T) (k : ℕ) :
    (P.truncate k).SupportedOn T := by
  induction k generalizing ℓ P T with
  | zero => trivial
  | succ k ih =>
    cases P with
    | zero => exact (ih (supportedOn_zero T)).lift (Finset.empty_subset T)
    | cons S L₁ next =>
      obtain ⟨hS, hnext⟩ := hP
      exact ⟨hS, fun v => ih (hnext v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
/-- A presentation on `V_T` takes its values in `V_T`. -/
theorem SupportedOn.proj_eval {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (x : ι → F) : proj T (P.eval x) = P.eval x := by
  induction P generalizing T x with
  | zero => simp
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    simp only [eval_cons, map_add, L₁.proj_apply_of_subset hS]
    rw [← ih _ (hnext _) (proj Sᶜ x), proj_proj_of_subset' Finset.sdiff_subset]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
theorem SupportedOn.proj_eval_of_subset {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (h : T ⊆ U) (x : ι → F) : proj U (P.eval x) = P.eval x := by
  rw [← hP.proj_eval x, proj_proj_of_subset' h, hP.proj_eval]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
theorem SupportedOn.proj_eval_of_disjoint {P : CLFun F ι ℓ} {T U : Finset ι}
    (hP : P.SupportedOn T) (h : Disjoint U T) (x : ι → F) : proj U (P.eval x) = 0 := by
  rw [← hP.proj_eval x, proj_proj_of_disjoint h]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
/-- The two components of the prefix `L_{≤(k+1)}(x) = L₁ x + r` of a presentation
`cons S L₁ next` on `V_T`: `L₁ x` on `V_S`, and `r`, the prefix of the continuation, on
`V_{T \ S}`. -/
theorem SupportedOn.proj_eval_truncate_succ {S : Finset ι} {L₁ : RegLinear F S}
    {next : (ι → F) → CLFun F ι ℓ} {T : Finset ι} (hP : (cons S L₁ next).SupportedOn T)
    (k : ℕ) (x : ι → F) :
    proj S (((cons S L₁ next).truncate (k + 1)).eval x) = L₁ x ∧
      proj Sᶜ (((cons S L₁ next).truncate (k + 1)).eval x) =
        ((next (L₁ x)).truncate k).eval (proj Sᶜ x) := by
  obtain ⟨hS, hnext⟩ := hP
  have hr := (hnext (L₁ x)).truncate k
  have hsub : T \ S ⊆ Sᶜ := fun i hi => by
    simp only [Finset.mem_sdiff] at hi
    simpa using hi.2
  rw [truncate_succ_cons, eval_cons]
  constructor
  · rw [map_add, L₁.proj_apply, hr.proj_eval_of_disjoint Finset.disjoint_sdiff, add_zero]
  · rw [map_add, L₁.proj_compl_apply, zero_add, hr.proj_eval_of_subset hsub]
end
end MIPRE.CL.CLFun

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

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- The projectors are self-adjoint. -/
theorem proj_conjTranspose (hw : IsWeylFamily w) (e : n → F) : (proj w e)ᴴ = proj w e := by
  classical
  rw [proj_def w e, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.conjTranspose_smul, hw.selfAdjoint a, star_sgn]]
  congr 1
  simp
end
end MIPRE.Weyl

namespace MIPRE.CL.CLFun
section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- An honest output's first register and remainder recover the two construction branches. -/
theorem SupportedOn.proj_eval_cons {S T : Finset ι} {L : RegLinear F S}
    {next : (ι → F) → CLFun F ι ℓ} (hP : (cons S L next).SupportedOn T) (z : ι → F) :
    proj S ((cons S L next).eval z) = L z ∧
      proj Sᶜ ((cons S L next).eval z) = (next (L z)).eval (proj Sᶜ z) := by
  have h := hP.proj_eval_truncate_succ ℓ z
  simpa only [truncate_self] using h
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The sampling check can compute the honest marginal from the complete claimed output. -/
theorem SupportedOn.outputPrefix_eval {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (z : ι → F) :
    P.outputPrefix k (P.eval z) = (P.truncate k).eval z := by
  induction P generalizing T k z with
  | zero => cases k <;> simp [outputPrefix]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨hfirst, hrest⟩ := hP.proj_eval_cons z
      rw [outputPrefix_cons, hfirst, hrest, truncate_succ_cons, eval_cons,
        ih _ (hP.2 _) k (proj Sᶜ z)]
end
end MIPRE.CL.CLFun

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
/-- Jointly reading two commuting projective measurements gives a projective measurement. -/
theorem joint_measurement_isPVM {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (P : A → Matrix ι ι ℂ) (Q : B → Matrix ι ι ℂ) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ a b, Commute (P a) (Q b)) : IsPVM (fun ab : A × B => P ab.1 * Q ab.2) where
  isSelfAdjoint ab := by
    rw [Matrix.conjTranspose_mul, hP.isSelfAdjoint, hQ.isSelfAdjoint]
    exact (hc ab.1 ab.2).eq.symm
  idem ab := by
    rw [mul_assoc, ← mul_assoc (Q ab.2), (hc ab.1 ab.2).eq.symm,
      mul_assoc (P ab.1), hQ.idem, ← mul_assoc, hP.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hQ.sum_eq_one, mul_one]
    exact hP.sum_eq_one
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
/-- The sampling and hiding readouts used by the honest introspection strategy form a PVM. -/
theorem sampling_hiding_isPVM
    (L R : (Fin n → F) →ₗ[F] (Fin n → F)) (hLR : CL.perp R.ker ≤ L.ker) :
    IsPVM (fun ab : (Fin n → F) × (Fin n → F) => synOf wZ L ab.1 * synOf wX R ab.2) :=
  joint_measurement_isPVM _ _ (linear_measurement_isPVM wZ isWeylFamily_wZ L)
    (linear_measurement_isPVM wX isWeylFamily_wX R) (linear_measurements_commute L R hLR)
end
end MIPRE.Introspection

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
theorem adaptiveTensor_isPVM (P : A → Matrix I I ℂ) (Q : A → B → Matrix J J ℂ)
    (hP : IsPVM P) (hQ : ∀ a, IsPVM (Q a)) : IsPVM (adaptiveTensor P Q) where
  isSelfAdjoint ab := by
    simp only [adaptiveTensor, Matrix.conjTranspose_kronecker,
      hP.isSelfAdjoint, (hQ _).isSelfAdjoint]
  idem ab := by
    simp only [adaptiveTensor, ← Matrix.mul_kronecker_mul, hP.idem, (hQ _).idem]
  sum_eq_one := by
    simp only [adaptiveTensor, Fintype.sum_prod_type]
    simp_rw [← kronecker_sum_right, (hQ _).sum_eq_one]
    rw [← sum_kronecker_left, hP.sum_eq_one, Matrix.one_kronecker_one]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem localRead_isPVM {S : Finset ι} (L : CL.RegLinear F S) : IsPVM (localRead L) := by
  apply sampling_hiding_isPVM
  simp only [CL.ker_lperp, CL.perp_perp]
  exact le_rfl
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem stopHide_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (V : Finset ι) :
    IsPVM (stopHide P V) := by
  have hX : IsPVM (proj (wX (F := F) (n := V))) :=
    ⟨proj_conjTranspose isWeylFamily_wX,
      fun x => by rw [proj_mul_proj isWeylFamily_wX, if_pos rfl], sum_proj isWeylFamily_wX⟩
  exact hX.coarse (stopHideAnswer P V)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
/-- Projectivity of every honest hiding level, including the branch-dependent later levels. -/
theorem hideRegister_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) : IsPVM (hideRegister P k V h) := by
  induction P generalizing V k with
  | zero => cases k <;> exact stopHide_isPVM _ _
  | cons S L next ih =>
      cases k with
      | zero => exact stopHide_isPVM _ _
      | succ k =>
          exact registerOp_isPVM (coordinateSplit S V h.1)
            ((adaptiveTensor_isPVM (localRead L) _ (localRead_isPVM L)
              (fun z => ih _ _ _ (h.2 _))).coarse (joinHide S))
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem hideOp_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) : IsPVM (hideOp P k h) :=
  registerOp_isPVM _ (hideRegister_isPVM P k _ h)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]
theorem hideOp_marginal {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) (y : ι → F) :
    (∑ yp : (ι → F) × (ι → F), hideOp P k h (y, yp)) = readout (P.truncate k).eval y := by
  unfold hideOp
  rw [← registerOp_sum, hideRegister_marginal]
  ext x x'
  simp [readout, registerOp_apply, Matrix.diagonal_apply]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
theorem registerOp_commute (e : I ≃ J) {P Q : Matrix J J ℂ} (hc : Commute P Q) :
    Commute (registerOp e P) (registerOp e Q) := by
  show _ * _ = _ * _
  rw [← registerOp_mul, ← registerOp_mul, hc.eq]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideOp_commute_next (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) (a b : HideLabel F ι) :
    Commute (hideOp P k h a) (hideOp P (k + 1) h b) :=
  registerOp_commute _ (hideRegister_commute_next P k _ h a b)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
theorem registerOp_ne_zero (e : I ≃ J) (P : Matrix J J ℂ) : registerOp e P ≠ 0 ↔ P ≠ 0 := by
  constructor
  · intro h he
    exact h (he ▸ rfl)
  · intro h he
    have hh := congrArg (registerOp e.symm) he
    rw [registerOp_inv] at hh
    exact h hh
end
end MIPRE.Introspection.Honest

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
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The next dual readout depends only on the preceding reported prefix. -/
theorem dualReadout_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    dualReadout P k (P.outputPrefix k y) x = dualReadout P k y x := by
  induction P generalizing T k y with
  | zero => simp [dualReadout]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨hfirst, hrest⟩ := proj_outputPrefix_cons hP k y
      simp only [dualReadout]
      rw [hfirst, hrest, ih _ (hP.2 _) k _]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Every rejected actual adjacent hiding comparison has zero honest operator product. -/
theorem hideOp_reject_next_zero (P : CL.CLFun F ι ℓ) (k : ℕ) (hk : k + 1 < ℓ)
    (h : P.SupportedOn Finset.univ) (a b : HideLabel F ι)
    (hab : ¬ CLChecks.hidingNext P k a b) : hideOp P k h a * hideOp P (k + 1) h b = 0 := by
  by_contra hn
  apply hab
  apply hideRegister_accepts_next P k hk Finset.univ h a b
  exact (registerOp_ne_zero univRestriction _).mp (by simpa only [hideOp, registerOp_mul] using hn)
end
end MIPRE.Introspection.Honest

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

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The next ideal Z prefix commutes with every actual preceding honest Hide
operator, including prefixes whose readout projector is zero. -/
theorem hidingPrefixOp_commute_hideOp (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (y : Option (ι → F)) (a : HideLabel F ι) :
    Commute (hidingPrefixOp P (k + 1) y) (hideOp P k h a) := by
  cases y with
  | none => rw [hidingPrefixOp_none]; exact Commute.zero_left _
  | some y =>
    rw [hidingPrefixOp_some, ← hideOp_marginal P (k + 1) h y]
    apply Commute.sum_left
    intro b _
    exact (hideOp_commute_next P k h a (y, b)).symm
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideOp_entry_prefix (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) (x x' : ι → F)
    (ha : hideOp P k h a x x' ≠ 0) : (P.truncate k).eval x = a.1 := by
  have he := hideRegister_entry_nonzero P k univ h a
    (univRestriction x) (univRestriction x') ha
  simpa using he
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideOp_prefix_fixed (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) (ha : hideOp P k h a ≠ 0) :
    P.outputPrefix k a.1 = a.1 := by
  have hex : ∃ x x', hideOp P k h a x x' ≠ 0 := by
    by_contra hn
    apply ha
    ext x x'
    exact not_not.mp (by simpa using not_exists.mp (not_exists.mp hn x) x')
  obtain ⟨x, x', hx⟩ := hex
  rw [← hideOp_entry_prefix P k h a x x' hx, ← h.outputPrefix_eval]
  exact CLChecks.outputPrefix_outputPrefix h _ le_rfl
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem readout_mul_hideOp (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (y : ι → F) (a : HideLabel F ι) :
    readout (P.truncate k).eval y * hideOp P k h a =
      if a.1 = y then hideOp P k h a else 0 := by
  ext x x'
  rw [readout, Matrix.diagonal_mul]
  by_cases he : hideOp P k h a x x' = 0
  · by_cases hy : a.1 = y <;> simp [he, hy]
  · rw [hideOp_entry_prefix P k h a x x' he]
    by_cases hy : a.1 = y <;> simp [hy]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The next prefix selects exactly the conditioning key of an honest next
Hide outcome. The fixed-prefix property is proved from matrix support. -/
theorem hidingPrefixOp_mul_next (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (y : Option (ι → F)) (a : HideLabel F ι) :
    hidingPrefixOp P (k + 1) y * hideOp P (k + 1) h a =
      if (hideLabelNext P k a).1 = y then hideOp P (k + 1) h a else 0 := by
  by_cases ha : hideOp P (k + 1) h a = 0
  · simp [ha]
  have hfix := hideOp_prefix_fixed P (k + 1) h a ha
  cases y with
  | none => simp [hideLabelNext, hideLabelAnswer, TypedEstimates.hidingNextLater,
      TypedEstimates.hidingNextCondition]
  | some y =>
    rw [hidingPrefixOp_some, readout_mul_hideOp]
    simp only [hideLabelNext, hideLabelAnswer, TypedEstimates.hidingNextLater,
      TypedEstimates.hidingNextCondition, hfix, Option.some.injEq]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem hideLabel_guarded_of_check (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a b : HideLabel F ι)
    (hab : CLChecks.hidingNext P k a b) :
    TypedEstimates.hidingNextGuarded P k (hideLabelNext P k b).1 (hideLabelCoarse P k a) =
      (hideLabelNext P k b).2 := by
  have hmatch : P.outputPrefix k a.1 = P.outputPrefix k (P.outputPrefix (k + 1) b.1) := by
    rw [CLChecks.outputPrefix_outputPrefix h _ (by omega)]
    exact hab.1
  unfold hideLabelNext hideLabelCoarse hideLabelAnswer
  change TypedEstimates.hidingNextGuarded P k (some (P.outputPrefix (k + 1) b.1)) _ = _
  rw [TypedEstimates.hidingNextGuarded_factor h k a.1 a.2.1 a.2.2 _ hmatch]
  simp only [TypedEstimates.hidingNextEarlier, TypedEstimates.hidingNextLater,
    TypedEstimates.hidingNextCondition, Option.map_some,
    CLChecks.dualReadout_outputPrefix h,
    show k + 2 = (k + 1) + 1 by omega, CLChecks.prefixRegister_outputPrefix_succ h]
  exact congrArg some (Prod.ext hab.1 (Prod.ext hab.2.2.2.symm hab.2.2.1))
end
end MIPRE.Introspection.Honest

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.Honest
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution (P : CL.CLFun F ι ℓ) (k : ℕ)
    (hk : k + 1 < ℓ) (h : P.SupportedOn univ)
    (p : Option (ι → F) × Option (HideLabel F ι)) :
    conditionalIdeal (hideOp P k h) (hidingPrefixOp P (k + 1))
      (fun y a => TypedEstimates.hidingNextGuarded P k y (hideLabelCoarse P k a)) p =
        fibSum (hideOp P (k + 1) h) (hideLabelNext P k) p := by
  have he := conditionalIdeal_eq_coarse_of_reject (hideOp P k h) (hideOp P (k + 1) h)
    (hidingPrefixOp P (k + 1))
    (fun y a => TypedEstimates.hidingNextGuarded P k y (hideLabelCoarse P k a))
    (hideLabelNext P k) (hideOp_isPVM P k h) (hideOp_isPVM P (k + 1) h)
    (hidingPrefixOp_commute_hideOp P k h) (hidingPrefixOp_mul_next P k h)
    (by
      intro a b hab
      apply hideOp_reject_next_zero P k hk h a b
      intro hcheck
      exact hab (hideLabel_guarded_of_check P k h a b hcheck)) p
  refine he.trans ?_
  simp only [fibSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : hideLabelNext P k a = p <;> simp [ha]
end MIPRE.Introspection.Honest
