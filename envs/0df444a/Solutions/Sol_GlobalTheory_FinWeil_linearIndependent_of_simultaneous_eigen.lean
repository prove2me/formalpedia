-- Prove2me | solution 1 for GlobalTheory.FinWeil.linearIndependent_of_simultaneous_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:09:18.705675+00:00
-- url     : https://prove2.me/submissions/63bf62ee-4188-462e-95b0-7e9b0b1a1a9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentOfJointEigenvectors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Theorems.Thm_GlobalTheory_JointEigenvectorsIndependent_linearIndependent_of_joint_eigenvectors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution {ι α M : Type} [AddCommGroup M] [Module ℂ M] (f : ι → M) (χ : ι → α → ℂ)
    (op : α → M →ₗ[ℂ] M) (hχ : Function.Injective χ) (hop : ∀ a i, op a (f i) = χ i a • f i) (hf : ∀ i, f i ≠ 0) :
    LinearIndependent ℂ f := by
  first
  | exact @_root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors
  | exact _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors
  | (apply _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors ..)
end GlobalTheory.FinWeil
