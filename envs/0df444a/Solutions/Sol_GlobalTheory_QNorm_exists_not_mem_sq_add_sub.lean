-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_not_mem_sq_add_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:43:50.178403+00:00
-- url     : https://prove2.me/submissions/5f8894ae-381c-49b9-9ab0-90798817e559

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitEvenOrderQuadraticNormValuesOneModFour
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ρ : 𝓞 F, ∀ a : 𝓞 F, a ^ 2 + a - ρ ∉ v.asIdeal := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  let f : 𝓞 F ⧸ v.asIdeal → 𝓞 F ⧸ v.asIdeal := fun x => x ^ 2 + x
  have hni : ¬ Function.Injective f := by
    intro h
    have h0 : (0 : 𝓞 F ⧸ v.asIdeal) = -1 := h (by simp [f])
    exact one_ne_zero (neg_eq_zero.mp h0.symm)
  have hns : ¬ Function.Surjective f := fun hs => hni (Finite.injective_iff_surjective.mpr hs)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨r, hr⟩ := hns
  obtain ⟨ρ, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨ρ, fun a ha => hr (Ideal.Quotient.mk _ a) ?_⟩
  have h := (Ideal.Quotient.eq_zero_iff_mem).mpr ha
  simp only [map_sub, map_add, map_pow] at h
  exact sub_eq_zero.mp h
end GlobalTheory.QNorm
