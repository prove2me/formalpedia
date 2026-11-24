-- Prove2me | solution 1 for GlobalTheory.GalMean.exists_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:43.266409+00:00
-- url     : https://prove2.me/submissions/e4dfdd9a-7f36-4575-b3a9-c91d2d85a857

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeanLogNormConjugatesOverIdealClasses
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.GalMean
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
namespace GlobalTheory.GalMean
theorem _root_.solution {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (a b : ℂ)
    (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) :
    ∃ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L ∧ IsGalois ℚ L ∧ (∀ x : K, φK x ∈ L) ∧ a ∈ L ∧ b ∈ L := by
  set R : IntermediateField ℚ ℂ := φK.toRatAlgHom.fieldRange
  set A : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({a, b} : Set ℂ)
  have h1 : FiniteDimensional ℚ R :=
    (AlgEquiv.ofInjectiveField φK.toRatAlgHom).toLinearEquiv.finiteDimensional
  have h2 : FiniteDimensional ℚ A := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    rcases hx with rfl | hx
    · exact ha.isIntegral
    · rw [Set.mem_singleton_iff.1 hx]; exact hb.isIntegral
  set M : IntermediateField ℚ ℂ := R ⊔ A
  have : FiniteDimensional ℚ M := IntermediateField.finiteDimensional_sup _ _
  have hn : IsNormalClosure ℚ M (IntermediateField.normalClosure ℚ M ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun x => IsAlgClosed.splits _)
  have : Normal ℚ (IntermediateField.normalClosure ℚ M ℂ) := hn.normal
  have hle : M ≤ IntermediateField.normalClosure ℚ M ℂ := IntermediateField.le_normalClosure M
  have hR : R ≤ M := le_sup_left
  have hA : A ≤ M := le_sup_right
  refine ⟨_, inferInstance, {}, fun x => hle (hR ⟨x, rfl⟩), hle (hA (IntermediateField.subset_adjoin ℚ _ (by simp))),
    hle (hA (IntermediateField.subset_adjoin ℚ _ (by simp)))⟩
end GlobalTheory.GalMean
