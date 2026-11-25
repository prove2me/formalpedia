-- Prove2me | solution 1 for GlobalTheory.GenericExtend.extAt_of_coheight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:47:16.891809+00:00
-- url     : https://prove2.me/submissions/5ef6a313-aad3-4e99-9397-bfe4e180b486

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_GlobalTheory_GenericExtend_exists_lift
import Theorems.Thm_GlobalTheory_GenericExtend_exists_specializes_mem_range
import Theorems.Thm_GlobalTheory_GenericExtend_extAt_of_generic
import Theorems.Thm_GlobalTheory_GenericExtend_exists_unit_dvr
import Theorems.Thm_GlobalTheory_GenericExtend_appLE_inv_eq
import Theorems.Thm_GlobalTheory_DvrModel_isIntegral
import Theorems.Thm_GlobalTheory_DvrModel_isLocallyNoetherian
import Theorems.Thm_GlobalTheory_DvrModel_isOpenImmersion_generic
import Theorems.Thm_GlobalTheory_PrimeSection_isDiscreteValuationRing_stalk
import Theorems.Thm_GlobalTheory_genericPoint_mem_opens
import Theorems.Thm_GlobalTheory_isIntegral_of_geometricallyIntegral
import Theorems.Thm_GlobalTheory_isIso_stalkMap_of_flat_of_surjectiveOnStalks
import Theorems.Thm_GlobalTheory_isNormalScheme_of_smooth
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend
namespace GlobalTheory.GenericExtend
theorem _root_.solution {X U P : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {N : LB P}
    (hN : N.IsLB) {eU : U ⟶ pullback p j} (w : eU ≫ pullback.fst p j = j ≫ e)
    (hπ : eU ≫ pullback.snd p j = 𝟙 U)
    {τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N _ τ)
    {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a))
    (y : P) (hx : Order.coheight (p y) = 1) (a : N.ι) (ha : y ∈ N.U a) :
    ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
      ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := by
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst p j)
  have := IsNormalScheme.of_isIso_stalkMap (pullback.fst p j)
  have := IsNormalScheme.isDiscreteValuationRing_stalk hx
  let V : Type := X.presheaf.stalk (p y)
  let K : Type := FractionRing V
  let l : Spec (.of V) ⟶ X := X.fromSpecStalk (p y)
  have : IsPreimmersion l := inferInstanceAs (IsPreimmersion (X.fromSpecStalk (p y)))
  have hl : Set.range l = {ξ | ξ ⤳ p y} := Scheme.range_fromSpecStalk
  let n : Spec (.of K) ⟶ Spec (.of V) := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨κ, hκ⟩ := exists_lift j (n ≫ l) (by
    rintro _ ⟨o, rfl⟩
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    obtain ⟨v, rfl⟩ : ξ ∈ Set.range l := hl ▸ hξy
    have hv : n o ⤳ v := (PrimeSpectrum.le_iff_specializes (n o) v).1 (by
      intro c hc
      have hc' : algebraMap V K c ∈ o.asIdeal := hc
      rw [Ideal.eq_bot_of_prime o.asIdeal, Ideal.mem_bot,
        map_eq_zero_iff _ (IsFractionRing.injective V K)] at hc'
      rw [hc']
      exact Ideal.zero_mem _)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range (hv.map l.continuous) hξ)
  let φ := pullback.fst p l
  let f := pullback.snd p l
  let k := pullback.fst f n
  let fK := pullback.snd f n
  have hK : IsPullback k fK f n := .of_hasPullback f n
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral hK
  have := DvrModel.isOpenImmersion_generic hK
  let ψ : pullback f n ⟶ pullback p j := pullback.lift (k ≫ φ) (fK ≫ κ) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hK.w, Category.assoc, Category.assoc,
      hκ])
  have hψ : ψ ≫ pullback.fst p j = k ≫ φ := pullback.lift_fst _ _ _
  have hψ' : ψ ≫ pullback.snd p j = fK ≫ κ := pullback.lift_snd _ _ _
  let eV : Spec (.of V) ⟶ pullback p l := pullback.lift (l ≫ e) (𝟙 _) (by simp [he])
  have heV : eV ≫ φ = l ≫ e := pullback.lift_fst _ _ _
  have heV' : eV ≫ f = 𝟙 _ := pullback.lift_snd _ _ _
  let eK : Spec (.of K) ⟶ pullback f n := pullback.lift (n ≫ eV) (𝟙 _) (by simp [heV'])
  have heK : eK ≫ k = n ≫ eV := pullback.lift_fst _ _ _
  have heK' : eK ≫ fK = 𝟙 _ := pullback.lift_snd _ _ _
  have hek : eK ≫ ψ = κ ≫ eU := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hψ, reassoc_of% heK, heV, Category.assoc, w, reassoc_of% hκ]
    · rw [Category.assoc, hψ', reassoc_of% heK', Category.assoc, hπ, Category.comp_id]
  have hW : ∀ A : P.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ pullback.fst p j ⁻¹ᵁ A := fun A ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hψ]
  obtain ⟨s, hu⟩ := exists_unit_dvr hK hN hψ hW heV heV' heK hτ (ρ := ρ) (fun z a hz ↦ by
    rw [hek, hρ, hκ]
    rw [← Scheme.Hom.comp_apply κ, hκ]
    exact hz) a
  obtain ⟨h, hh⟩ : y ∈ Set.range φ := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hl]
    exact specializes_rfl
  obtain ⟨z, hz⟩ : genericPoint (pullback p l :) ∈ k.opensRange :=
    have : Nonempty k.opensRange := ⟨⟨k (Nonempty.some inferInstance), _, rfl⟩⟩
    genericPoint_mem_opens _
  have hg : ∀ y, y ⤳ φ h → φ (k z) ⤳ y := fun y hy ↦ by
    obtain ⟨h', rfl⟩ : y ∈ Set.range φ := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hl]
      exact (hh ▸ hy).map p.continuous
    rw [hz]
    exact (genericPoint_specializes h').map φ.continuous
  have ha' : φ h ∈ N.U a := by rw [hh]; exact ha
  have hza : z ∈ k ⁻¹ᵁ φ ⁻¹ᵁ N.U a := (hg _ specializes_rfl).mem_open (N.U a).isOpen ha'
  suffices H : ExtAt (pullback.fst p j) (N.U a) (τ a).val (φ h) ∧
      ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val (φ h) by rwa [hh] at H
  exact ⟨extAt_of_generic _ φ k ψ hψ _ _ _ le_rfl (hW _) (appLE_inv_eq _ hu).1 z hza h ha' hg,
    extAt_of_generic _ φ k ψ hψ _ _ _ le_rfl (hW _) (appLE_inv_eq _ hu).2 z hza h ha' hg⟩
end GlobalTheory.GenericExtend
