-- Prove2me | solution 1 for GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:46:26.438832+00:00
-- url     : https://prove2.me/submissions/2c19a755-b328-4cc3-91fb-a1730d3824b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsIsFractionRingStalkImageOfGenericPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheafDescent
namespace GlobalTheory.NormSheafDescent
theorem _root_.solution : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  intro Y Z π _ _ U hU hUr h
  set ζ := genPt π with hζ
  have hcl : (U : Set Z) ⊆ closure {ζ} := by
    rintro _ hx
    obtain ⟨y, rfl⟩ := hUr hx
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes y).map π.continuous)
  have hirr : IsIrreducible (U : Set Z) :=
    ⟨⟨ζ, h⟩, (isIrreducible_singleton.closure).isPreirreducible.open_subset U.isOpen hcl⟩
  obtain ⟨hD, -⟩ := GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hirr
  refine ⟨hD, ?_⟩
  letI := algAK π U h
  have hl := hU.isLocalization_stalk ⟨ζ, h⟩
  have hbot : (hU.primeIdealOf ⟨ζ, h⟩).asIdeal = ⊥ := by
    let q : PrimeSpectrum Γ(Z, U) := ⟨⊥, Ideal.bot_prime⟩
    have hq : hU.fromSpec q ∈ U := hU.range_fromSpec.le ⟨_, rfl⟩
    have hs : hU.fromSpec (hU.primeIdealOf ⟨ζ, h⟩) ⤳ hU.fromSpec q := by
      rw [hU.fromSpec_primeIdealOf]
      exact specializes_iff_mem_closure.mpr (hcl hq)
    have hs' := hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.mp hs
    exact le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ q).mpr hs')
  have hc : (hU.primeIdealOf ⟨ζ, h⟩).asIdeal.primeCompl = nonZeroDivisors Γ(Z, U) := by
    ext x; simp [hbot, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  unfold IsLocalization.AtPrime at hl
  rw [hc] at hl
  exact hl
end GlobalTheory.NormSheafDescent
