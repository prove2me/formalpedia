-- Prove2me | solution 1 for GlobalTheory.PolModLattice.univ_aut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:12.145698+00:00
-- url     : https://prove2.me/submissions/fd9a87d4-3a34-407d-a7d7-82bfd93f8ce0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
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
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open Classical
namespace GlobalTheory.PolModLattice
theorem _root_.solution : (Finset.univ : Finset (E ≃ₐ[maximalRealSubfield E] E)) = {1, IsCMField.complexConj E} := by
  have hc : Nat.card (E ≃ₐ[maximalRealSubfield E] E) = 2 :=
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E) ▸ IsGalois.card_aut_eq_finrank _ E
  obtain ⟨τ, hτ, hu⟩ := (Nat.card_eq_two_iff' 1).1 hc
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr (by rw [hu σ h, hu _ (IsCMField.complexConj_ne_one E)])
end GlobalTheory.PolModLattice
