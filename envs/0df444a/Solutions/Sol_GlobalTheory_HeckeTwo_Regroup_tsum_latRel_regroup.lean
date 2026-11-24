-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:50.654903+00:00
-- url     : https://prove2.me/submissions/16f33d1f-1bfc-4ec3-9d6b-0dd3fdc0b605

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroup
import Theorems.Thm_GlobalTheory_HeckeTwo_Regroup_regroupMap_injective
import Theorems.Thm_GlobalTheory_HeckeTwo_Regroup_regroupMap_surjective
import Theorems.Thm_GlobalTheory_HeckeTwo_Regroup_g_out

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
namespace GlobalTheory.HeckeTwo.Regroup
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (g : F × F → ℂ), (∀ (ε : (NumberField.RingOfIntegers F)ˣ) (a b : F), g (((ε : NumberField.RingOfIntegers F) : F) * a, ((ε : NumberField.RingOfIntegers F) : F) * b) = g (a, b)) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => g c.out.1) → Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)) => g (c.out.1, 0)) ∧ (∀ c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => g (a.1, c.out.1))) ∧ Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1)) ∧ ∑' c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟), g c.out.1 = ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)), g (c.out.1, 0) + ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1) := by
  intro F _ _ 𝔞 𝔟 g hg hs
  open GlobalTheory.HeckeTwo.Regroup in
  let e := Equiv.ofBijective _ ⟨regroupMap_injective 𝔞 𝔟, regroupMap_surjective 𝔞 𝔟⟩
  let h : Quotient (unitRel (latM 𝔞)) ⊕
      (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), {a : F // a ∈ latM 𝔞}) → ℂ :=
    Sum.elim (fun c => g (c.out.1, 0)) (fun s => g (s.2.1, s.1.out.1))
  have hfe : (fun c : Quotient (latRel 𝔞 𝔟) => g c.out.1) ∘ e = h := by
    funext x
    rcases x with c | ⟨c, a⟩
    · exact GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _
    · exact GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _
  have hsh : Summable h := hfe ▸ (e.summable_iff).2 hs
  have hl : Summable (h ∘ Sum.inl) := hsh.comp_injective Sum.inl_injective
  have hr : Summable (h ∘ Sum.inr) := hsh.comp_injective Sum.inr_injective
  have hr' : Summable (fun s : (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)),
      {a : F // a ∈ latM 𝔞}) => g (s.2.1, s.1.out.1)) := hr
  refine ⟨hl, fun c => hr'.sigma_factor c, hr'.sigma, ?_⟩
  rw [← e.tsum_eq, show (∑' x, g (e x).out.1) = ∑' x, h x from congrArg tsum hfe, hl.tsum_sum hr]
  exact congrArg₂ (· + ·) rfl hr'.tsum_sigma
end GlobalTheory.HeckeTwo.Regroup
