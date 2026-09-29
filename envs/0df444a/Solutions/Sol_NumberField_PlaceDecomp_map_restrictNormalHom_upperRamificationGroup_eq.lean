-- Prove2me | solution 1 for NumberField.PlaceDecomp.map_restrictNormalHom_upperRamificationGroup_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fc3c5a61-c337-528c-b711-8759851e29f6

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Theorems.Thm_NumberField_PlaceDecomp_lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers
import Theorems.Thm_NumberField_PlaceDecomp_map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_map_restrictNormalHom_upperRamificationGroup_eq
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_map_restrictNormalHom_upperRamificationGroup_eq.NumberField"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_map_restrictNormalHom_upperRamificationGroup_eq.NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "mk PlaceDecomp.exists_restrict_decomp_surjective_of_tower PlaceDecomp.faithfulSMul_decomp PlaceDecomp.lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers PlaceDecomp.map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp coe_smul_integers exists_restrict_decomp_surjective_of_tower faithfulSMul_decomp lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict"
namespace HerbAsm
p2m_open "NumberField.PlaceDecomp NumberField"

theorem upperRamificationGroup_congr {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    {G : Type*} [Group G] [MulSemiringAction G R] [MulSemiringAction G S]
    (h : ∀ i, IsLocalRing.lowerRamificationGroup R G i = IsLocalRing.lowerRamificationGroup S G i) (u : ℚ) :
    IsLocalRing.upperRamificationGroup R G u = IsLocalRing.upperRamificationGroup S G u := by
  have hcard : IsLocalRing.lowerRamificationCard R G = IsLocalRing.lowerRamificationCard S G := by
    funext i; unfold IsLocalRing.lowerRamificationCard; rw [h]
  have hphi : IsLocalRing.herbrandPhi R G = IsLocalRing.herbrandPhi S G := by
    funext v; unfold IsLocalRing.herbrandPhi; rw [hcard]
  have hidx : IsLocalRing.upperRamificationIndex R G u = IsLocalRing.upperRamificationIndex S G u := by
    unfold IsLocalRing.upperRamificationIndex; rw [hphi]
  unfold IsLocalRing.upperRamificationGroup
  rw [hidx, h]

theorem map_upperRamificationGroup_eq_of_forall_map_lower_eq
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    {G G' : Type*} [Group G] [MulSemiringAction G R] [Group G'] [MulSemiringAction G' S]
    (f : G ≃* G')
    (h : ∀ i, (IsLocalRing.lowerRamificationGroup R G i).map f.toMonoidHom = IsLocalRing.lowerRamificationGroup S G' i)
    (u : ℚ) :
    (IsLocalRing.upperRamificationGroup R G u).map f.toMonoidHom = IsLocalRing.upperRamificationGroup S G' u := by
  have hcard : IsLocalRing.lowerRamificationCard R G = IsLocalRing.lowerRamificationCard S G' := by
    funext i
    unfold IsLocalRing.lowerRamificationCard
    rw [← h i]
    exact Nat.card_congr ((IsLocalRing.lowerRamificationGroup R G i).equivMapOfInjective f.toMonoidHom f.injective).toEquiv
  have hphi : IsLocalRing.herbrandPhi R G = IsLocalRing.herbrandPhi S G' := by
    funext v; unfold IsLocalRing.herbrandPhi; rw [hcard]
  have hidx : IsLocalRing.upperRamificationIndex R G u = IsLocalRing.upperRamificationIndex S G' u := by
    unfold IsLocalRing.upperRamificationIndex; rw [hphi]
  unfold IsLocalRing.upperRamificationGroup
  rw [hidx]
  exact h _

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

set_option quotPrecheck false in
local notation "O_w" => (w.adicCompletionIntegers F)
set_option quotPrecheck false in
local notation "D_w" => (decomp E F w)

theorem upperRamificationQuotientCompat (H : Subgroup ↥D_w) [H.Normal] :
    IsLocalRing.UpperRamificationQuotientCompat (↥O_w) (↥D_w) (↥(FixedPoints.subring (↥O_w) (↥H))) H := by
  haveI := faithfulSMul_integers E F w
  haveI := finite_residueField F w
  haveI := liesOver F w ↥D_w
  haveI : PerfectField (IsLocalRing.ResidueField ↥O_w) := PerfectField.ofFinite
  haveI : Algebra.IsSeparable
      (↥(FixedPoints.subring (↥O_w) ↥D_w) ⧸ IsLocalRing.maximalIdeal ↥(FixedPoints.subring (↥O_w) ↥D_w))
      (↥O_w ⧸ IsLocalRing.maximalIdeal ↥O_w) := by
    haveI : Finite (↥O_w ⧸ IsLocalRing.maximalIdeal ↥O_w) := finite_residueField F w
    haveI : Finite (↥(FixedPoints.subring (↥O_w) ↥D_w) ⧸ IsLocalRing.maximalIdeal ↥(FixedPoints.subring (↥O_w) ↥D_w)) :=
      Finite.of_injective _ (algebraMap _ (↥O_w ⧸ IsLocalRing.maximalIdeal ↥O_w)).injective
    haveI : PerfectField (↥(FixedPoints.subring (↥O_w) ↥D_w) ⧸ IsLocalRing.maximalIdeal ↥(FixedPoints.subring (↥O_w) ↥D_w)) :=
      PerfectField.ofFinite
    haveI : Module.Finite (↥(FixedPoints.subring (↥O_w) ↥D_w) ⧸ IsLocalRing.maximalIdeal ↥(FixedPoints.subring (↥O_w) ↥D_w))
        (↥O_w ⧸ IsLocalRing.maximalIdeal ↥O_w) := Module.Finite.of_finite
    haveI : Algebra.IsAlgebraic (↥(FixedPoints.subring (↥O_w) ↥D_w) ⧸ IsLocalRing.maximalIdeal ↥(FixedPoints.subring (↥O_w) ↥D_w))
        (↥O_w ⧸ IsLocalRing.maximalIdeal ↥O_w) := Algebra.IsAlgebraic.of_finite _ _
    infer_instance
  exact IsDiscreteValuationRing.upperRamificationQuotientCompat_of_isSeparable_residueField H

end frame

end NumberField.PlaceDecomp.HerbAsm

open _root_.NumberField.PlaceDecomp _root_.P2MW.S_NumberField_PlaceDecomp_map_restrictNormalHom_upperRamificationGroup_eq.NumberField.PlaceDecomp in
theorem solution
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [Normal E L]
    (w : HeightOneSpectrum (𝓞 F)) (u : ℚ) (hu : 0 ≤ u) :
    (((((w.valuation F).valuationSubring).upperRamificationGroup E u).map
        (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype).map
        (AlgEquiv.restrictNormalHom L : (F ≃ₐ[E] F) →* (L ≃ₐ[E] L))) =
      ((((w.under (𝓞 L)).valuation L).valuationSubring).upperRamificationGroup E u).map
        ((((w.under (𝓞 L)).valuation L).valuationSubring).decompositionSubgroup E).subtype := by
  classical
  obtain ⟨r, hsurj, hr, -, -, -⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E L F w

  have h1F : ValuationSubring.upperRamificationGroup E ((w.valuation F).valuationSubring) u =
      IsLocalRing.upperRamificationGroup ↥(w.adicCompletionIntegers F) ↥(decomp E F w) u :=
    HerbAsm.upperRamificationGroup_congr
      (fun i => NumberField.PlaceDecomp.lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers E F w i) u
  have h1L : ValuationSubring.upperRamificationGroup E (((w.under (𝓞 L)).valuation L).valuationSubring) u =
      IsLocalRing.upperRamificationGroup ↥((w.under (𝓞 L)).adicCompletionIntegers L) ↥(decomp E L (w.under (𝓞 L))) u :=
    HerbAsm.upperRamificationGroup_congr
      (fun i => NumberField.PlaceDecomp.lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers E L (w.under (𝓞 L)) i) u

  have h3 : (IsLocalRing.upperRamificationGroup ↥(w.adicCompletionIntegers F) ↥(decomp E F w) u).map (QuotientGroup.mk' r.ker) =
      IsLocalRing.upperRamificationGroup ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥r.ker) (↥(decomp E F w) ⧸ r.ker) u :=
    HerbAsm.upperRamificationQuotientCompat E F w r.ker u hu

  have h2 : (IsLocalRing.upperRamificationGroup ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥r.ker)
        (↥(decomp E F w) ⧸ r.ker) u).map (QuotientGroup.quotientKerEquivOfSurjective r hsurj).toMonoidHom =
      IsLocalRing.upperRamificationGroup ↥((w.under (𝓞 L)).adicCompletionIntegers L) ↥(decomp E L (w.under (𝓞 L))) u :=
    HerbAsm.map_upperRamificationGroup_eq_of_forall_map_lower_eq _
      (fun i => NumberField.PlaceDecomp.map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict
        E L F w r hsurj hr i) u

  have hfac : (AlgEquiv.restrictNormalHom L : (F ≃ₐ[E] F) →* (L ≃ₐ[E] L)).comp (decomp E F w).subtype =
      ((decomp E L (w.under (𝓞 L))).subtype.comp (QuotientGroup.quotientKerEquivOfSurjective r hsurj).toMonoidHom).comp
        (QuotientGroup.mk' r.ker) := by
    refine MonoidHom.ext fun σ => ?_
    show AlgEquiv.restrictNormalHom L (σ : F ≃ₐ[E] F) =
      ((QuotientGroup.quotientKerEquivOfSurjective r hsurj (QuotientGroup.mk σ) : ↥(decomp E L (w.under (𝓞 L)))) : L ≃ₐ[E] L)
    rw [← hr σ]
    rfl
  rw [h1F, Subgroup.map_map, hfac, ← Subgroup.map_map, ← Subgroup.map_map, h3, h2, ← h1L]

end S_NumberField_PlaceDecomp_map_restrictNormalHom_upperRamificationGroup_eq
end P2MW
export P2MW.S_NumberField_PlaceDecomp_map_restrictNormalHom_upperRamificationGroup_eq (solution)
