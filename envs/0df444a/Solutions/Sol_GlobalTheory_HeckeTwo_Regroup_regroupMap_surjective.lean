-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.Regroup.regroupMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:41:43.293099+00:00
-- url     : https://prove2.me/submissions/47b42d96-47f6-44a8-a726-d039872d8950

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroup
import Theorems.Thm_GlobalTheory_HeckeTwo_Regroup_unit_mul_mem
import Theorems.Thm_GlobalTheory_HeckeTwo_Regroup_mk_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.Regroup
variable {F : Type} [Field F] [NumberField F]
variable (𝔞 𝔟 : Frac F)
namespace GlobalTheory.HeckeTwo.Regroup
theorem _root_.solution : Function.Surjective (regroupMap 𝔞 𝔟) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
  obtain ⟨⟨a, b⟩, ha, hb, hne⟩ := p
  by_cases hb0 : b = 0
  · subst hb0
    have ha0 : a ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨ε, hε⟩ : (unitRel (latM 𝔞)).r ⟨a, ha, ha0⟩ (Quotient.mk (unitRel (latM 𝔞)) ⟨a, ha, ha0⟩).out :=
      Quotient.exact (Quotient.out_eq _).symm
    exact ⟨Sum.inl (Quotient.mk _ ⟨a, ha, ha0⟩), (mk_eq 𝔞 𝔟 ε hε (mul_zero _).symm).symm⟩
  · obtain ⟨ε, hε⟩ : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r ⟨b, hb, hb0⟩
        (Quotient.mk (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ⟨b, hb, hb0⟩).out :=
      Quotient.exact (Quotient.out_eq _).symm
    exact ⟨Sum.inr ⟨Quotient.mk _ ⟨b, hb, hb0⟩, ⟨_, unit_mul_mem ε ha⟩⟩, (mk_eq 𝔞 𝔟 ε rfl hε).symm⟩
end GlobalTheory.HeckeTwo.Regroup
