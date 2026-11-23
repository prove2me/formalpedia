-- Prove2me | solution 1 for GlobalTheory.DivLin.baseChange_skew_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:15.931213+00:00
-- url     : https://prove2.me/submissions/f747c52f-99fd-4fcc-a6de-ebe97ba19187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
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
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.DivLin
variable {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I]
  (R : Type) [CommRing R] [Algebra O R]
namespace GlobalTheory.DivLin
theorem _root_.solution (B : LinearMap.BilinForm O H) {M M' : Module.End O H}
    (hskew : ∀ x y, B (M x) y + B x (M y) = 0) (hiso : ∀ x y, B (M x) (M' y) = 0) (x y : R ⊗[O] H) :
    B.baseChange R (M.baseChange R x) y + B.baseChange R x (M.baseChange R y) = 0 ∧
      B.baseChange R (M.baseChange R x) (M'.baseChange R y) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply]
    exact ⟨by linear_combination h₁.1 + h₂.1, by linear_combination h₁.2 + h₂.2⟩
  | tmul c₀ a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add]
      exact ⟨by linear_combination h₁.1 + h₂.1, by linear_combination h₁.2 + h₂.2⟩
    | tmul c' b =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]
      rw [← add_smul, hskew, hiso]
      simp
end GlobalTheory.DivLin
