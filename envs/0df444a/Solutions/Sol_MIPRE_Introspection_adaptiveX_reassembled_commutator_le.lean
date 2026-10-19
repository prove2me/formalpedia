-- Prove2me | solution 1 for MIPRE.Introspection.adaptiveX_reassembled_commutator_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:41:15.017739+00:00
-- url     : https://prove2.me/submissions/4f12b24b-8377-4b10-b869-b40c184793b9

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveXTest.lean (solution of MIPRE.Introspection.adaptiveX_reassembled_commutator_le);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixLaw
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixConditioning
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixMixing
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveZFactor
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
import Definitions.Def_MIPRE_Foundations_Introspection_ReadRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualMarginal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXSplit
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDualFactor
import Definitions.Def_MIPRE_Foundations_Introspection_ProductStageReadTests
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveXTest
import Theorems.Thm_MIPRE_Introspection_CLChecks_dualReadout_proj_compl_prefix
import Theorems.Thm_MIPRE_Introspection_CLChecks_truncate_fibre_of_agree
import Theorems.Thm_MIPRE_Introspection_Honest_dualRegister_factor
import Theorems.Thm_MIPRE_Introspection_Honest_pauliX_entry
import Theorems.Thm_MIPRE_Introspection_Honest_readDualOp_eq_registerDual
import Theorems.Thm_MIPRE_Introspection_Honest_readout_ambientSplit
import Theorems.Thm_MIPRE_Introspection_Honest_synX_split_second
import Theorems.Thm_MIPRE_Introspection_norm_evec_comp_equiv
import Theorems.Thm_MIPRE_Introspection_prefixProjector_weight
import Theorems.Thm_MIPRE_Introspection_prefixResidual_reassembled_commutator
import Theorems.Thm_MIPRE_Introspection_registerEPR_equiv
import Theorems.Thm_MIPRE_Introspection_registerOp_kronecker
import Theorems.Thm_MIPRE_Introspection_registerOp_mulVec
import Theorems.Thm_MIPRE_Introspection_residualDualOp_stage
import Theorems.Thm_MIPRE_mulVec_kron_expVec
import Theorems.Thm_MIPRE_norm_evec_expVec
import Theorems.Thm_MIPRE_sgn_add

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateSqNorm ψ M :=
  sq_nonneg _
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix
open scoped Kronecker
variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- A product operator's squared state norm factors over a product state. -/
theorem stateSqNorm_expVec_kron (ψ : V × W → ℂ) (ξ : H × K → ℂ)
    (Q : Matrix V V ℂ) (A : Matrix H H ℂ) :
    stateSqNorm (expVec ψ ξ) (Q ⊗ₖ A) = stateSqNorm ψ Q * stateSqNorm ξ A := by
  unfold stateSqNorm stateNorm stateVec
  change ‖evec _‖ ^ 2 = ‖evec _‖ ^ 2 * ‖evec _‖ ^ 2
  rw [mulVec_kron_expVec, norm_evec_expVec, mul_pow]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {I J K L A : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
  [Fintype A] [DecidableEq A]
/-- State distances are unchanged by independent permutations of the two parties. -/
theorem stateSqNorm_registerOp (e : I ≃ J) (f : K ≃ L)
    (ψ : J × L → ℂ) (M : Matrix J J ℂ) :
    stateSqNorm (ψ ∘ e.prodCongr f) (registerOp e M) = stateSqNorm ψ M := by
  unfold stateSqNorm stateNorm stateVec
  change ‖evec _‖ ^ 2 = ‖evec _‖ ^ 2
  rw [← registerOp_one f, ← registerOp_kronecker, registerOp_mulVec, norm_evec_comp_equiv]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- EPR on a product basis factors exactly into the two EPR states. -/
theorem registerEPR_prod :
    registerEPR (I × J) = expVec (registerEPR I) (registerEPR J) := by
  funext p
  obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := p
  simp only [registerEPR, expVec, Prod.mk.injEq, Fintype.card_prod, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), _root_.mul_inv_rev, Complex.ofReal_mul]
  by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj, mul_comm]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- The EPR factorization under the actual party-wise register permutation. -/
theorem registerState_split (e : I ≃ J × R) (ξ : H × K → ℂ) :
    registerState I ξ =
      registerState J (registerState R ξ) ∘
        (registerParty e H).prodCongr (registerParty e K) := by
  have h := registerEPR_equiv e
  rw [registerEPR_prod] at h
  funext p
  have hp := congrFun h (p.1.1, p.2.1)
  change registerEPR I (p.1.1, p.2.1) * ξ (p.1.2, p.2.2) =
    registerEPR J ((e p.1.1).1, (e p.2.1).1) *
      (registerEPR R ((e p.1.1).2, (e p.2.1).2) * ξ (p.1.2, p.2.2))
  rw [← hp]
  exact mul_assoc _ _ _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]
/-- A local operator has exactly the same error in the split register presentation. -/
theorem stateSqNorm_registerState_split (e : I ≃ J × R) (ξ : H × K → ℂ)
    (M : Matrix (J × (R × H)) (J × (R × H)) ℂ) :
    stateSqNorm (registerState I ξ) (registerOp (registerParty e H) M) =
      stateSqNorm (registerState J (registerState R ξ)) M := by
  rw [registerState_split e ξ, stateSqNorm_registerOp]
end
end MIPRE.Introspection

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F I J K : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
/-- Any additive split preserving the coordinate pairing splits the X spectral projector. -/
theorem pauliX_split
    (e : (I → F) ≃ (J → F) × (K → F))
    (hadd : ∀ a b, e (a + b) = ((e a).1 + (e b).1, (e a).2 + (e b).2))
    (hdot : ∀ a b, trDot a b = trDot (e a).1 (e b).1 + trDot (e a).2 (e b).2)
    (z : I → F) :
    proj wX z = registerOp e (proj wX (e z).1 ⊗ₖ proj wX (e z).2) := by
  have hc : Fintype.card (I → F) = Fintype.card (J → F) * Fintype.card (K → F) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  ext x y
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, pauliX_entry,
    hdot, hadd, sgn_add, hc, Nat.cast_mul, _root_.mul_inv_rev]
  ring
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem truncate_fibre_congr {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x x' : ι → F)
    (hag : ∀ i ∈ prefixRegister P k y, x i = x' i) :
    (P.truncate k).eval x = y ↔ (P.truncate k).eval x' = y :=
  ⟨truncate_fibre_of_agree hP k y x x' hag,
    truncate_fibre_of_agree hP k y x' x (fun i hi => (hag i hi).symm)⟩
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem truncate_fibre_proj {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    (P.truncate k).eval x = y ↔
      (P.truncate k).eval (CL.proj (prefixRegister P k y) x) = y :=
  truncate_fibre_congr hP k y x _ (fun i hi => by simp [CL.proj_apply, hi])
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem insertRegister_ambientSplit (V : Finset ι) (x : ι → F) :
    insertRegister V (ambientSplit V x).1 = CL.proj V x := by
  ext i
  simp [insertRegister, ambientSplit, CL.proj_apply]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The adaptive ideal prefix has no action on unused coordinates. This is
an exact matrix identity for every claimed prefix, including empty fibres. -/
theorem hidingPrefixOp_factor [Algebra (ZMod 2) F]
    (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ) (y : ι → F) :
    hidingPrefixOp P k (some y) = registerOp (ambientSplit (CLChecks.prefixRegister P k y))
      (prefixProjector P k y ⊗ₖ
        (1 : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ ℂ)) := by
  rw [hidingPrefixOp_some]
  apply readout_ambientSplit
  intro x
  rw [insertRegister_ambientSplit]
  exact CLChecks.truncate_fibre_proj hP k y x
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem trDot_univRestriction (x y : ι → F) :
    trDot (univRestriction x) (univRestriction y) = trDot x y := by
  unfold trDot
  congr 1
  exact Equiv.sum_comp univIndex (fun i => x i * y i)
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem pauliX_univRestriction (z : ι → F) :
    registerOp univRestriction (proj wX (univRestriction z)) = proj wX z := by
  have hc := Fintype.card_congr (univRestriction (F := F) (ι := ι))
  ext x y
  simp only [registerOp_apply, pauliX_entry, ← hc]
  change _ * sgn (trDot (univRestriction (x + y)) (univRestriction z)) = _
  rw [trDot_univRestriction]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
theorem registerParty_kron_one {I J R H : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
    (e : I ≃ J × R) (Q : Matrix J J ℂ) :
    registerOp (registerParty e H) (Q ⊗ₖ (1 : Matrix (R × H) (R × H) ℂ)) =
      (aOp (registerOp e (Q ⊗ₖ (1 : Matrix R R ℂ))) : Matrix (I × H) _ ℂ) := by
  ext ⟨i, h⟩ ⟨j, h'⟩
  simp only [registerOp_apply, registerParty, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodAssoc_apply, aOp, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases hr : (e i).2 = (e j).2 <;> by_cases hh : h = h' <;> simp [hr, hh]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- Exact conditional error, on the concrete complement of the used prefix
register. It holds for every prefix, including impossible ones of weight zero. -/
theorem stateSqNorm_prefixResidualOp (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (ξ : H × K → ℂ)
    (M : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    stateSqNorm (registerState (ι → F) ξ) (prefixResidualOp P k y M) =
      prefixWeight P k y *
        stateSqNorm (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ) M := by
  rw [prefixResidualOp, stateSqNorm_registerState_split]
  change stateSqNorm
    (expVec (registerEPR (CLChecks.prefixRegister P k y → F))
      (registerState (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ξ))
    (prefixProjector P k y ⊗ₖ M) = _
  rw [stateSqNorm_expVec_kron, prefixProjector_weight P hP k y]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
/-- The global commutation error equals the actual prefix-weighted local
commutation error, even when ideal outcome types depend on the prefix. -/
theorem prefixResidual_reassembled_commutator_sum (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    {A : Type*} [Fintype A] {B : (ι → F) → Type*} [∀ y, Fintype (B y)]
    (M : (y : ι → F) → A → Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (N : (y : ι → F) → B y → Matrix ((stageRemaining P k y → F) × H) _ ℂ) :
    (∑ a, ∑ p : (y : ι → F) × B y, stateSqNorm (registerState (ι → F) ξ)
      ((∑ z, prefixResidualOp P k z (M z a)) * prefixResidualOp P k p.1 (N p.1 p.2) -
        prefixResidualOp P k p.1 (N p.1 p.2) * (∑ z, prefixResidualOp P k z (M z a)))) =
      ∑ y, prefixWeight P k y * ∑ a, ∑ b,
        stateSqNorm (registerState (stageRemaining P k y → F) ξ)
          (M y a * N y b - N y b * M y a) := by
  simp only [Fintype.sum_sigma, prefixResidual_reassembled_commutator P hP,
    stateSqNorm_prefixResidualOp P hP]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
end
end MIPRE.Introspection

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F I J K Y : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype Y] [DecidableEq Y]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem trDot_ambientSplit (V : Finset ι) (x y : ι → F) :
    trDot x y = trDot (ambientSplit V x).1 (ambientSplit V y).1 +
      trDot (ambientSplit V x).2 (ambientSplit V y).2 := by
  unfold trDot
  rw [← map_add]
  congr 1
  have he := Equiv.sum_comp (ambientIndexSplit V).symm (fun i : ι => x i * y i)
  rw [Fintype.sum_sum_type] at he
  exact he.symm
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F I J K Y : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype Y] [DecidableEq Y]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem pauliX_ambientSplit (V : Finset ι) (x : ι → F) :
    proj wX x = registerOp (ambientSplit V)
      (proj wX (ambientSplit V x).1 ⊗ₖ proj wX (ambientSplit V x).2) :=
  pauliX_split (ambientSplit V) (fun _ _ => rfl) (trDot_ambientSplit V) x
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F I J K Y : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype Y] [DecidableEq Y]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem insertRegister_ambientSplit_snd (V : Finset ι) (x : ι → F) :
    insertRegister Vᶜ (ambientSplit V x).2 = CL.proj Vᶜ x := by
  ext i
  simp [insertRegister, ambientSplit, CL.proj_apply]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F I J K Y : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype Y] [DecidableEq Y]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The selected dual readout has no action on preceding prefix registers. -/
theorem dualReadout_prefix_split {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn univ) (k : ℕ) (y yp : ι → F) :
    synOf wX (CLChecks.dualReadout P k y) yp =
      registerOp (ambientSplit (CLChecks.prefixRegister P k y))
        ((1 : Matrix (CLChecks.prefixRegister P k y → F) _ ℂ) ⊗ₖ
          synOf wX (fun x : ↥((CLChecks.prefixRegister P k y)ᶜ) → F =>
            CLChecks.dualReadout P k y (insertRegister (CLChecks.prefixRegister P k y)ᶜ x)) yp) := by
  have hf (x : ι → F) : CLChecks.dualReadout P k y x =
      CLChecks.dualReadout P k y (insertRegister (CLChecks.prefixRegister P k y)ᶜ
        (ambientSplit (CLChecks.prefixRegister P k y) x).2) := by
    rw [insertRegister_ambientSplit_snd, CLChecks.dualReadout_proj_compl_prefix h]
  conv_lhs => arg 2; ext x; rw [hf x]
  exact synX_split_second (ambientSplit (CLChecks.prefixRegister P k y))
    (pauliX_ambientSplit (F := F) (CLChecks.prefixRegister P k y))
    (fun x => CLChecks.dualReadout P k y (insertRegister (CLChecks.prefixRegister P k y)ᶜ x)) yp
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem synX_univRestriction {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : (ι → F) → Y) (y : Y) :
    registerOp univRestriction (synOf wX (fun x => f (insertRegister univ x)) y) =
      synOf wX f y := by
  ext x x'
  simp only [registerOp_apply, synOf, Matrix.sum_apply, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (univRestriction (F := F) (ι := ι))
  intro z
  simp only [insertRegister_univ]
  by_cases hz : f z = y
  · simp only [hz, if_true]
    exact (congrArg (fun M => M x x') (pauliX_univRestriction z)).symm
  · simp [hz]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The source prefix/dual product is the existing honest Read dual marginal,
not a separately stipulated family. -/
theorem readDualOp_factor (P : CL.CLFun F ι ℓ) (h : P.SupportedOn univ)
    (k : ℕ) (y yp : ι → F) :
    readDualOp P k h (some (y,yp)) = hidingPrefixOp P k (some y) *
      synOf wX (CLChecks.dualReadout P k y) yp := by
  rw [readDualOp_eq_registerDual, dualRegister_factor, registerOp_mul, synX_univRestriction,
    hidingPrefixOp_some]
  congr 1
  ext x x'
  simp [registerOp_apply, readout, Matrix.diagonal_apply,
    univRestriction.injective.eq_iff]
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Full concrete tensor factorization under the prefix's own coordinate split,
valid uniformly at every CL stage and every claimed prefix/dual label. -/
theorem readDualOp_prefix_factor (P : CL.CLFun F ι ℓ) (h : P.SupportedOn univ)
    (k : ℕ) (y yp : ι → F) :
    readDualOp P k h (some (y,yp)) =
      registerOp (ambientSplit (CLChecks.prefixRegister P k y))
        (prefixProjector P k y ⊗ₖ residualDualOp P k y yp) := by
  rw [readDualOp_factor, hidingPrefixOp_factor P h, dualReadout_prefix_split P h,
    ← registerOp_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul]
  rfl
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
theorem aOp_registerOp_kron {I J R H : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
    (e : I ≃ J × R) (P : Matrix J J ℂ) (N : Matrix R R ℂ) :
    (aOp (registerOp e (P ⊗ₖ N)) : Matrix (I × H) _ ℂ) =
      registerOp (registerParty e H) (P ⊗ₖ (aOp N : Matrix (R × H) _ ℂ)) := by
  ext ⟨i,h⟩ ⟨j,h'⟩
  simp only [aOp, registerOp_apply, Matrix.kroneckerMap_apply, registerParty,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodAssoc_apply]
  exact mul_assoc _ _ _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {ι F H : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] {ℓ : ℕ}
/-- The actual honest dual family, including any auxiliary factor, is exactly
the prefix-conditioned current X-dual readout consumed by adaptive mixing. -/
theorem readDualOp_stage_factor (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    (aOp (readDualOp P k hP (some (y, coordinateInsert (P.factorOfPrefix k y) z))) :
      Matrix ((ι → F) × H) _ ℂ) =
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y)
        wX (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) z) := by
  rw [readDualOp_prefix_factor P hP, aOp_registerOp_kron, residualDualOp_stage P hP]
  unfold prefixResidualOp registerReadout
  rw [← registerParty_kron_one]
  rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem adaptiveDualLabel_injective (P : CL.CLFun F ι ℓ) (k : ℕ) :
    Function.Injective (adaptiveDualLabel P k) := by
  rintro ⟨y, z⟩ ⟨y', z'⟩ h
  have hp := Option.some.inj h
  have hy : y = y' := congrArg Prod.fst hp
  cases hy
  have hz : z = z' := by
    simpa only [coordinateRestrict_insert] using
      congrArg (coordinateRestrict (P.factorOfPrefix k y)) (congrArg Prod.snd hp)
  cases hz
  rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem adaptiveDualLabel_sum_le (P : CL.CLFun F ι ℓ) (k : ℕ)
    (f : Option ((ι → F) × (ι → F)) → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (∑ p, f (adaptiveDualLabel P k p)) ≤ ∑ z, f z := by
  have he : (∑ z ∈ univ.image (adaptiveDualLabel P k), f z) =
      ∑ p, f (adaptiveDualLabel P k p) := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => adaptiveDualLabel_injective P k h
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun z _ _ => hf z)
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι H K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}
theorem _root_.solution (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    {A : Type*} [Fintype A]
    (M : (y : ι → F) → A → Matrix ((stageRemaining P k y → F) × H) _ ℂ) :
    (∑ y, prefixWeight P k y * ∑ a, ∑ z,
      stateSqNorm (registerState (stageRemaining P k y → F) ξ)
        (M y a * registerReadout (stageSplit P hP k y)
            wX (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) z -
          registerReadout (stageSplit P hP k y)
            wX (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) z * M y a)) ≤
      ∑ a, ∑ z, stateSqNorm (registerState (ι → F) ξ)
        ((∑ y, prefixResidualOp P k y (M y a)) *
            (aOp (Honest.readDualOp P k hP z) : Matrix ((ι → F) × H) _ ℂ) -
          (aOp (Honest.readDualOp P k hP z) : Matrix ((ι → F) × H) _ ℂ) *
            (∑ y, prefixResidualOp P k y (M y a))) := by
  rw [← prefixResidual_reassembled_commutator_sum P hP k ξ M
    (fun y z => registerReadout (H := H) (stageSplit P hP k y)
      wX (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) z)]
  apply Finset.sum_le_sum
  intro a _
  have hs := adaptiveDualLabel_sum_le P k
    (fun z => stateSqNorm (registerState (ι → F) ξ)
      ((∑ y, prefixResidualOp P k y (M y a)) *
          (aOp (Honest.readDualOp P k hP z) : Matrix ((ι → F) × H) _ ℂ) -
        (aOp (Honest.readDualOp P k hP z) : Matrix ((ι → F) × H) _ ℂ) *
          (∑ y, prefixResidualOp P k y (M y a))))
    (fun _ => stateSqNorm_nonneg _ _)
  simpa only [adaptiveDualLabel, readDualOp_stage_factor] using hs
end MIPRE.Introspection
