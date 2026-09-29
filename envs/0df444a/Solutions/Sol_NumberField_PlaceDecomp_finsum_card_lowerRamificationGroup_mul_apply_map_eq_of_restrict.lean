-- Prove2me | solution 1 for NumberField.PlaceDecomp.finsum_card_lowerRamificationGroup_mul_apply_map_eq_of_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8821670f-8e09-5f7f-ba0f-0ad610b7de55

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Theorems.Thm_NumberField_PlaceDecomp_lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers
import Theorems.Thm_NumberField_PlaceDecomp_map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict
import Theorems.Thm_IsDiscreteValuationRing_finsum_card_lowerRamificationGroup_mul_apply_map_mk_eq_of_apply_bot_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_finsum_card_lowerRamificationGroup_mul_apply_map_eq_of_restrict
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_finsum_card_lowerRamificationGroup_mul_apply_map_eq_of_restrict.NumberField"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_finsum_card_lowerRamificationGroup_mul_apply_map_eq_of_restrict.NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "mk place PlaceDecomp.decomp PlaceDecomp.faithfulSMul_decomp PlaceDecomp.lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers PlaceDecomp.map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp coe_smul_integers faithfulSMul_decomp lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict"
namespace HerbAsm
p2m_open "NumberField.PlaceDecomp NumberField"

theorem coe_smul_integers {E F : Type} [Field E] [Field F] [NumberField F] [Algebra E F] {w : HeightOneSpectrum (𝓞 F)}
    (σ : ↥(decomp E F w)) (x : ↥(w.adicCompletionIntegers F)) :
    ((σ • x : ↥(w.adicCompletionIntegers F)) : w.adicCompletion F) = σ • (x : w.adicCompletion F) := rfl

section frame
attribute [local instance] Ideal.Quotient.field

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F))

theorem faithfulSMul_integers : FaithfulSMul ↥(decomp E F w) ↥(w.adicCompletionIntegers F) := by
  haveI := NumberField.PlaceDecomp.faithfulSMul_decomp E F w
  refine ⟨fun {σ τ} h => ?_⟩
  apply eq_of_smul_eq_smul (α := w.adicCompletion F)
  intro x
  rcases ValuationSubring.mem_or_inv_mem (w.adicCompletionIntegers F) x with hx | hx
  · have := congrArg (fun t : ↥(w.adicCompletionIntegers F) => (t : w.adicCompletion F)) (h ⟨x, hx⟩)
    simpa only [coe_smul_integers] using this
  · have h' := congrArg (fun t : ↥(w.adicCompletionIntegers F) => (t : w.adicCompletion F)) (h ⟨x⁻¹, hx⟩)
    simp only [coe_smul_integers, smul_inv''] at h'
    exact inv_injective h'

theorem finite_residueField : Finite (IsLocalRing.ResidueField ↥(w.adicCompletionIntegers F)) := by
  haveI : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  exact IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers F w

theorem liesOver (M : Type) [Monoid M] [MulSemiringAction M ↥(w.adicCompletionIntegers F)] :
    (IsLocalRing.maximalIdeal ↥(w.adicCompletionIntegers F)).LiesOver
      (IsLocalRing.maximalIdeal ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) M)) := by
  refine ⟨?_⟩
  rw [Ideal.under_def, FixedPoints.maximalIdeal_subring_eq_comap]
  rfl

end frame

end NumberField.PlaceDecomp.HerbAsm

open _root_.NumberField.PlaceDecomp _root_.P2MW.S_NumberField_PlaceDecomp_finsum_card_lowerRamificationGroup_mul_apply_map_eq_of_restrict.NumberField.PlaceDecomp in
theorem solution
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [Normal E L]
    (w : HeightOneSpectrum (𝓞 F))
    (r : ↥(NumberField.PlaceDecomp.decomp E F w) →* ↥(NumberField.PlaceDecomp.decomp E L (w.under (𝓞 L))))
    (hsurj : Function.Surjective r)
    (hr : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E F w),
      ((r σ : ↥(NumberField.PlaceDecomp.decomp E L (w.under (𝓞 L)))) : L ≃ₐ[E] L) =
        AlgEquiv.restrictNormalHom L (σ : F ≃ₐ[E] F))
    (f : Subgroup ↥(NumberField.PlaceDecomp.decomp E L (w.under (𝓞 L))) → ℚ) (hf : f ⊥ = 0) :
    (ValuationSubring.lowerRamificationGroup E ((w.valuation F).valuationSubring) 0).map r =
        ValuationSubring.lowerRamificationGroup E (((w.under (𝓞 L)).valuation L).valuationSubring) 0 ∧
    ∑ᶠ i : ℕ,
        (Nat.card (ValuationSubring.lowerRamificationGroup E ((w.valuation F).valuationSubring) (i + 1)) : ℚ) /
            (Nat.card (ValuationSubring.lowerRamificationGroup E ((w.valuation F).valuationSubring) 0) : ℚ) *
          f ((ValuationSubring.lowerRamificationGroup E ((w.valuation F).valuationSubring) (i + 1)).map r) =
      ∑ᶠ j : ℕ,
        (Nat.card (ValuationSubring.lowerRamificationGroup E (((w.under (𝓞 L)).valuation L).valuationSubring) (j + 1)) : ℚ) /
            (Nat.card (ValuationSubring.lowerRamificationGroup E (((w.under (𝓞 L)).valuation L).valuationSubring) 0) : ℚ) *
          f (ValuationSubring.lowerRamificationGroup E (((w.under (𝓞 L)).valuation L).valuationSubring) (j + 1)) := by
  classical

  haveI := HerbAsm.faithfulSMul_integers E F w
  haveI := HerbAsm.finite_residueField F w
  haveI := HerbAsm.liesOver F w ↥(decomp E F w)
  haveI : Algebra.IsSeparable
      (↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥(decomp E F w)) ⧸
        IsLocalRing.maximalIdeal ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥(decomp E F w)))
      (↥(w.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal ↥(w.adicCompletionIntegers F)) := by
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal ↥(w.adicCompletionIntegers F))
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥(decomp E F w)))
    haveI : Finite (↥(w.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal ↥(w.adicCompletionIntegers F)) :=
      HerbAsm.finite_residueField F w
    haveI : Finite (↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥(decomp E F w)) ⧸
        IsLocalRing.maximalIdeal ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥(decomp E F w))) :=
      Finite.of_injective _ (algebraMap _ (↥(w.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal ↥(w.adicCompletionIntegers F))).injective
    haveI : PerfectField (↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥(decomp E F w)) ⧸
        IsLocalRing.maximalIdeal ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥(decomp E F w))) := PerfectField.ofFinite
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField

  let e := QuotientGroup.quotientKerEquivOfSurjective r hsurj
  obtain ⟨h0, hsum⟩ :=
    IsDiscreteValuationRing.finsum_card_lowerRamificationGroup_mul_apply_map_mk_eq_of_apply_bot_eq_zero
      (R := ↥(w.adicCompletionIntegers F)) (G := ↥(decomp E F w)) r.ker
      (fun S => f (S.map e.toMonoidHom)) (by show f (Subgroup.map e.toMonoidHom ⊥) = 0; rw [Subgroup.map_bot]; exact hf)

  have hF : ∀ i, ValuationSubring.lowerRamificationGroup E ((w.valuation F).valuationSubring) i =
      IsLocalRing.lowerRamificationGroup ↥(w.adicCompletionIntegers F) ↥(decomp E F w) i :=
    NumberField.PlaceDecomp.lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers E F w
  have hL : ∀ j, ValuationSubring.lowerRamificationGroup E (((w.under (𝓞 L)).valuation L).valuationSubring) j =
      IsLocalRing.lowerRamificationGroup ↥((w.under (𝓞 L)).adicCompletionIntegers L) ↥(decomp E L (w.under (𝓞 L))) j :=
    NumberField.PlaceDecomp.lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers E L (w.under (𝓞 L))
  have hfix : ∀ i, (IsLocalRing.lowerRamificationGroup ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥r.ker)
        (↥(decomp E F w) ⧸ r.ker) i).map e.toMonoidHom =
      IsLocalRing.lowerRamificationGroup ↥((w.under (𝓞 L)).adicCompletionIntegers L) ↥(decomp E L (w.under (𝓞 L))) i :=
    NumberField.PlaceDecomp.map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict E L F w r hsurj hr

  have hr_fac : ∀ S : Subgroup ↥(decomp E F w), S.map r = (S.map (QuotientGroup.mk' r.ker)).map e.toMonoidHom := by
    intro S
    rw [Subgroup.map_map]
    congr 1
  refine ⟨?_, ?_⟩
  · rw [hF 0, hL 0, hr_fac, h0, hfix 0]
  · simp_rw [hF, hL]
    simp_rw [hr_fac]
    simp_rw [← hfix]
    have hcard : ∀ K' : Subgroup (↥(decomp E F w) ⧸ r.ker), Nat.card ↥(K'.map e.toMonoidHom) = Nat.card ↥K' :=
      fun K' => Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    simp_rw [hcard]
    exact hsum

end S_NumberField_PlaceDecomp_finsum_card_lowerRamificationGroup_mul_apply_map_eq_of_restrict
end P2MW
export P2MW.S_NumberField_PlaceDecomp_finsum_card_lowerRamificationGroup_mul_apply_map_eq_of_restrict (solution)
