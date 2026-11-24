-- Prove2me | solution 1 for GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:36:10.188827+00:00
-- url     : https://prove2.me/submissions/6ccb73bf-1ae4-4bcb-abda-966914196e51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFormCoefficientIdealMapLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsIsFractionRingStalkImageOfGenericPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffNormFormOfFamilyMemRangeIntegrallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoeffIdealFamilyMapBasicOpen
import Theorems.Thm_GlobalTheory_NormSheafDescent_isLocalization_away_of_eq_basicOpen
import Theorems.Thm_GlobalTheory_T_coeff_normFormOfFamily_mem_range_integrallyClosed
import Theorems.Thm_GlobalTheory_T_normFormCoefficientIdeal_map_localizationAway
import Theorems.Thm_GlobalTheory_T_sections_isFractionRing_stalk_imageOfGenericPoint


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
theorem _root_.solution : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y] [GlobalTheory.IsNormalScheme Z]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ Set.range π →
    (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      GlobalTheory.NormSheafDescent.famIdeal π hK hfd I (Z.affineBasicOpen f) := by
  intro Y Z π _ _ _ hK hfd I U f hU
  by_cases hD : genPt π ∈ Z.basicOpen f
  · have hζU : genPt π ∈ U.1 := Z.basicOpen_le f hD
    have hD' : genPt π ∈ (Z.affineBasicOpen f).1 := hD
    have hUD : ((Z.affineBasicOpen f : Z.affineOpens) : Set Z) ⊆ Set.range π :=
      fun x hx => hU (Z.basicOpen_le f hx)
    letI := fieldK π hK
    letI := algKL π
    obtain ⟨hdomA, hfrA⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π U.1 U.2 hU hζU
    obtain ⟨_, hfrA'⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π (Z.basicOpen f) (Z.affineBasicOpen f).2 hUD hD
    letI iA := algAK π U.1 hζU
    letI iB := algBL π U.1 hζU
    letI iA' := algAK π (Z.basicOpen f) hD
    letI iB' := algBL π (Z.basicOpen f) hD
    letI iAA' : Algebra Γ(Z, U) Γ(Z, Z.basicOpen f) :=
      (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom.toAlgebra
    have hleY : π ⁻¹ᵁ Z.basicOpen f ≤ π ⁻¹ᵁ U.1 := π.preimage_mono (Z.basicOpen_le f)
    letI iBB' : Algebra Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) :=
      (Y.presheaf.map (homOfLE hleY).op).hom.toAlgebra
    letI iAB : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1) := (π.app U.1).hom.toAlgebra
    haveI : IsLocalization.Away f Γ(Z, Z.basicOpen f) := U.2.isLocalization_basicOpen f
    haveI : IsLocalization.Away (algebraMap Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1) f) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) :=
      isLocalization_away_of_eq_basicOpen (U.2.preimage π) (π.app U.1 f) _
        (Scheme.preimage_basicOpen π f) hleY
    have h1 : (algebraMap Γ(Z, Z.basicOpen f) (Z.presheaf.stalk (genPt π))).comp
        (algebraMap Γ(Z, U) Γ(Z, Z.basicOpen f)) = algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π)) := by
      ext a
      exact Z.presheaf.germ_res_apply (homOfLE (Z.basicOpen_le f)) (genPt π) hD a
    have h2 : (algebraMap Γ(Y, π ⁻¹ᵁ Z.basicOpen f) Y.functionField).comp
        (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f)) =
          algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField := by
      ext a
      exact Y.presheaf.germ_res_apply (homOfLE hleY) (genericPoint Y) hD a
    have h3 : (algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp
        (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π))) =
          (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField).comp (algebraMap Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1)) := by
      ext a
      exact Scheme.Hom.germ_stalkMap_apply π U.1 (genericPoint Y) hζU a
    have h4 : Function.Injective (algebraMap Γ(Z, Z.basicOpen f) (Z.presheaf.stalk (genPt π))) :=
      IsFractionRing.injective _ _
    have h5 : ∀ {m : ℕ} (g : Fin m → Γ(Y, π ⁻¹ᵁ U.1)) s,
        (GlobalTheory.NormSheaf.normForm (Z.presheaf.stalk (genPt π)) Y.functionField
          (fun i => algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField (g i))).coeff s ∈
            (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π))).range := by
      intro m g s
      haveI : IsIntegrallyClosed Γ(Z, U) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen U.2
      letI iAL : Algebra Γ(Z, U) Y.functionField :=
        ((algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp
          (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π)))).toAlgebra
      haveI : IsScalarTower Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hfin : (π.app U.1).hom.Finite := π.finite_app U.1 U.2
      let φ : Γ(Y, π ⁻¹ᵁ U.1) →ₐ[Γ(Z, U)] Y.functionField :=
        { algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField with
          commutes' := fun a => (congrArg (fun h => h a) h3).symm }
      refine GlobalTheory.T.coeff_normFormOfFamily_mem_range_integrallyClosed Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField _ (fun i => ?_) s
      have hi : IsIntegral Γ(Z, U) (g i) := hfin.to_isIntegral (g i)
      exact hi.map φ
    have hJ : I.ideal ⟨π ⁻¹ᵁ (Z.affineBasicOpen f).1, (Z.affineBasicOpen f).2.preimage π⟩ =
        (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map
          (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f)) :=
      (I.map_ideal (U := ⟨π ⁻¹ᵁ (Z.affineBasicOpen f).1, (Z.affineBasicOpen f).2.preimage π⟩)
        (V := ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) hleY).symm
    simp only [famIdeal, dif_pos hζU, dif_pos hD']
    rw [hJ]
    exact GlobalTheory.T.normFormCoefficientIdeal_map_localizationAway Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField Γ(Y, π ⁻¹ᵁ U.1)
      Γ(Z, Z.basicOpen f) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) f h1 h2 h3 h4 h5 _
  · have hbot : Z.basicOpen f = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨y, rfl⟩ := hU (Z.basicOpen_le f hx)
      exact hD (((genericPoint_specializes y).map π.continuous).mem_open (Z.basicOpen f).isOpen hx)
    haveI : Subsingleton Γ(Z, Z.basicOpen f) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hbot)
    haveI : Subsingleton Γ(Z, (Z.affineBasicOpen f : Z.Opens)) := this
    ext x
    rw [Subsingleton.elim x 0]
    exact iff_of_true (Ideal.zero_mem _) (Ideal.zero_mem _)
end GlobalTheory.NormSheafDescent
