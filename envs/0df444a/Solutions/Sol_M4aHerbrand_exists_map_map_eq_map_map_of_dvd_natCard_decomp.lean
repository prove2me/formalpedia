-- Prove2me | solution 1 for M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/60bcc853-5c29-553a-a009-0272aa3917a8

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_exists_hom_res_inf_decomp_ideles_adicCompletion_apply
import Theorems.Thm_M4aHerbrand_exists_hom_res_inf_infPlaceDecomp_ideles_completion_apply
import Theorems.Thm_M4aHerbrand_map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp
import Theorems.Thm_M4aHerbrand_map_inclusion_map_subtype_map_ideles_eq_zero_infinitePlace_of_forall_eq_one
import Theorems.Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_res_ideles
import Theorems.Thm_IsGalois_map_two_units_injective_and_exists_of_map_subtype_eq_zero
import Theorems.Thm_M4aHerbrand_map_two_res_units_ideles_injective_of_isPGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_map_map_eq_map_map_of_dvd_natCard_decomp
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_map_map_eq_map_map_of_dvd_natCard_decomp.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart repHomOfMulEquivariant IdeleClassGroup IdeleGaloisDescent GenuineDescent.genuineBaseChange exists_hom_res_inf_decomp_ideles_adicCompletion_apply exists_hom_res_inf_infPlaceDecomp_ideles_completion_apply map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp map_inclusion_map_subtype_map_ideles_eq_zero_infinitePlace_of_forall_eq_one injective_and_finite_and_surjective_localCoordinates_groupCohomology_res_ideles map_two_res_units_ideles_injective_of_isPGroup"
namespace CaptureProof
p2m_open "M4aHerbrand"

theorem map_eq_map_of_hom_eq {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ B) (φ₂ : Rep.res f₂ A ⟶ B)
    (hφ : ∀ a : A, φ₁.hom a = φ₂.hom a) (n : ℕ) :
    groupCohomology.map f₁ φ₁ n = groupCohomology.map f₂ φ₂ n := by
  subst h
  obtain rfl : φ₁ = φ₂ := by
    ext a
    exact hφ a
  rfl

end M4aHerbrand.CaptureProof

theorem solution
    (E F L M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra E F] [Algebra E L] [Algebra E M] [Algebra F M] [Algebra L M]
    [IsScalarTower E F M] [IsScalarTower E L M] [IsGalois E F] [IsGalois E L] [IsGalois E M]
    (p : ℕ) [Fact p.Prime] (hM : IsPGroup p (M ≃ₐ[E] M))

    (DF : IdeleGaloisDescent (𝓞 F) E F) (DL : IdeleGaloisDescent (𝓞 L) E L) (DM : IdeleGaloisDescent (𝓞 M) E M)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactIF : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = DF.unitsAct g x)
    [MulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ]
    (hactIL : ∀ (g : (L ≃ₐ[E] L)) (x : (AdeleRing (𝓞 L) L)ˣ), g • x = DL.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)

    [MulDistribMulAction (F ≃ₐ[E] F) Fˣ]
    (hactF : ∀ (g : (F ≃ₐ[E] F)) (a : Fˣ), ((g • a : Fˣ) : F) = g (a : F))
    (jF : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
    (hjF : ∀ a : Fˣ, jF.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a))
    [MulDistribMulAction (L ≃ₐ[E] L) Lˣ]
    (hactL : ∀ (g : (L ≃ₐ[E] L)) (a : Lˣ), ((g • a : Lˣ) : L) = g (a : L))
    (jL : Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ ⟶ Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ)
    (hjL : ∀ a : Lˣ, jL.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a))

    (SF : Subgroup (M ≃ₐ[E] M)) [SF.Normal] (ιF : (M ≃ₐ[E] M) ⧸ SF ≃* (F ≃ₐ[E] F))
    (hιF : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ιF (QuotientGroup.mk g) x) = g (algebraMap F M x))
    (SL : Subgroup (M ≃ₐ[E] M)) [SL.Normal] (ιL : (M ≃ₐ[E] M) ⧸ SL ≃* (L ≃ₐ[E] L))
    (hιL : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ιL (QuotientGroup.mk g) y) = g (algebraMap L M y))

    (JF : Rep.res (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJF : ∀ x : (AdeleRing (𝓞 F) F)ˣ, JF.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))
    (JL : Rep.res (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJL : ∀ x : (AdeleRing (𝓞 L) L)ˣ, JL.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange L M).β.toMonoidHom x))

    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

    (α : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) 2))

    (hdiv : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype
          (prG (NumberField.PlaceAbove.above E F v)) 2).hom ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) jF 2).hom α) ≠ 0 →
      ∀ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 E) = v →
        Nat.card (F ≃ₐ[E] F) ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E L w')) :
    ∃ αL : ↥(groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) 2),
      (groupCohomology.map (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) JL 2).hom
          ((groupCohomology.map (MonoidHom.id (L ≃ₐ[E] L)) jL 2).hom αL) =
        (groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) JF 2).hom
          ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) jF 2).hom α) := by
  open M4aHerbrand.CaptureProof in
  classical

  have hactM : ∀ (g : M ≃ₐ[E] M) (a : Mˣ), ((g • a : Mˣ) : M) = g (a : M) := fun _ _ => rfl
  let fM : Mˣ →* (AdeleRing (𝓞 M) M)ˣ := Units.map (algebraMap M (AdeleRing (𝓞 M) M) : M →* AdeleRing (𝓞 M) M)
  have hfM : ∀ (g : M ≃ₐ[E] M) (a : Mˣ), fM (g • a) = g • fM a := fun g a => by
    rw [hactIM]
    apply Units.ext
    change algebraMap M (AdeleRing (𝓞 M) M) ((g • a : Mˣ) : M) = DM.act g (algebraMap M (AdeleRing (𝓞 M) M) (a : M))
    rw [hactM]
    exact (DM.compat g (a : M)).symm
  let jM : Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ ⟶ Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ :=
    M4aHerbrand.repHomOfMulEquivariant fM hfM
  have hjM : ∀ a : Mˣ, jM.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap M (AdeleRing (𝓞 M) M) : M →* AdeleRing (𝓞 M) M) a) :=
    fun _ => rfl
  let uF : Fˣ →* Mˣ := Units.map (algebraMap F M : F →* M)
  let uL : Lˣ →* Mˣ := Units.map (algebraMap L M : L →* M)
  let iF : Rep.res (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶ Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ :=
    Rep.ofHom ⟨(MonoidHom.toAdditive uF).toIntLinearMap, fun g => LinearMap.ext fun a => by
      change Additive.ofMul (uF (((ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) g) • (Additive.toMul : Additive Fˣ ≃ Fˣ) a)) = Additive.ofMul (g • uF ((Additive.toMul : Additive Fˣ ≃ Fˣ) a))
      congr 1
      apply Units.ext
      change algebraMap F M ((((ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) g) • (Additive.toMul : Additive Fˣ ≃ Fˣ) a : Fˣ) : F) = ((g • uF ((Additive.toMul : Additive Fˣ ≃ Fˣ) a) : Mˣ) : M)
      rw [hactF, hactM]
      exact hιF g _⟩
  have hiF : ∀ a : Fˣ, iF.hom (Additive.ofMul a) = Additive.ofMul (uF a) := fun _ => rfl
  let iL : Rep.res (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) ⟶ Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ :=
    Rep.ofHom ⟨(MonoidHom.toAdditive uL).toIntLinearMap, fun g => LinearMap.ext fun a => by
      change Additive.ofMul (uL (((ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) g) • (Additive.toMul : Additive Lˣ ≃ Lˣ) a)) = Additive.ofMul (g • uL ((Additive.toMul : Additive Lˣ ≃ Lˣ) a))
      congr 1
      apply Units.ext
      change algebraMap L M ((((ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) g) • (Additive.toMul : Additive Lˣ ≃ Lˣ) a : Lˣ) : L) = ((g • uL ((Additive.toMul : Additive Lˣ ≃ Lˣ) a) : Mˣ) : M)
      rw [hactL, hactM]
      exact hιL g _⟩
  have hiL : ∀ a : Lˣ, iL.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap L M : L →* M) a) := fun _ => rfl

  have sqF : ∀ β : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) 2,
      (groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) JF 2).hom ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) jF 2).hom β) =
        (groupCohomology.map (MonoidHom.id (M ≃ₐ[E] M)) jM 2).hom ((groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) iF 2).hom β) := fun β => by
    have h1 := congrArg (fun T => T.hom β) (groupCohomology.map_comp (MonoidHom.id (F ≃ₐ[E] F)) (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) jF JF 2)
    have h2 := congrArg (fun T => T.hom β) (groupCohomology.map_comp (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) (MonoidHom.id (M ≃ₐ[E] M)) iF jM 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
    rw [← h1, ← h2]
    have hgrp : (MonoidHom.id (F ≃ₐ[E] F)).comp (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) = (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)).comp (MonoidHom.id (M ≃ₐ[E] M)) := by ext; rfl
    refine congrArg
      (fun (T : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) 2 ⟶
          groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) 2) => T.hom β)
      (map_eq_map_of_hom_eq hgrp _ _ (fun a => ?_) 2)
    obtain ⟨x, rfl⟩ : ∃ x : Fˣ, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
    change JF.hom (jF.hom (Additive.ofMul x)) = jM.hom (iF.hom (Additive.ofMul x))
    have hL : JF.hom (jF.hom (Additive.ofMul x)) = Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom
        (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) x)) := by
      rw [hjF]; exact hJF _
    have hR : jM.hom (iF.hom (Additive.ofMul x)) = Additive.ofMul (fM (uF x)) := rfl
    have hmid : Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom
        (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) x) = fM (uF x) :=
      Units.ext ((M4aHerbrand.GenuineDescent.genuineBaseChange F M).β_compat (x : F))
    exact hL.trans ((congrArg Additive.ofMul hmid).trans hR.symm)
  have sqL : ∀ β : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) 2,
      (groupCohomology.map (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) JL 2).hom ((groupCohomology.map (MonoidHom.id (L ≃ₐ[E] L)) jL 2).hom β) =
        (groupCohomology.map (MonoidHom.id (M ≃ₐ[E] M)) jM 2).hom ((groupCohomology.map (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) iL 2).hom β) := fun β => by
    have h1 := congrArg (fun T => T.hom β) (groupCohomology.map_comp (MonoidHom.id (L ≃ₐ[E] L)) (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) jL JL 2)
    have h2 := congrArg (fun T => T.hom β) (groupCohomology.map_comp (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) (MonoidHom.id (M ≃ₐ[E] M)) iL jM 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
    rw [← h1, ← h2]
    have hgrp : (MonoidHom.id (L ≃ₐ[E] L)).comp (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) = (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)).comp (MonoidHom.id (M ≃ₐ[E] M)) := by ext; rfl
    refine congrArg
      (fun (T : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) 2 ⟶
          groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) 2) => T.hom β)
      (map_eq_map_of_hom_eq hgrp _ _ (fun a => ?_) 2)
    obtain ⟨x, rfl⟩ : ∃ x : Lˣ, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
    change JL.hom (jL.hom (Additive.ofMul x)) = jM.hom (iL.hom (Additive.ofMul x))
    have hL : JL.hom (jL.hom (Additive.ofMul x)) = Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange L M).β.toMonoidHom
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) x)) := by
      rw [hjL]; exact hJL _
    have hR : jM.hom (iL.hom (Additive.ofMul x)) = Additive.ofMul (fM (uL x)) := rfl
    have hmid : Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange L M).β.toMonoidHom
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) x) = fM (uL x) :=
      Units.ext ((M4aHerbrand.GenuineDescent.genuineBaseChange L M).β_compat (x : L))
    exact hL.trans ((congrArg Additive.ofMul hmid).trans hR.symm)

  obtain ⟨prH, hprH⟩ := M4aHerbrand.exists_hom_res_inf_decomp_ideles_adicCompletion_apply E M DM hactIM SL
  obtain ⟨prInfH, hprInfH⟩ := M4aHerbrand.exists_hom_res_inf_infPlaceDecomp_ideles_completion_apply E M DM hactIM SL
  have hz : (groupCohomology.map SL.subtype (𝟙 (Rep.res SL.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ))) 2).hom
      ((groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) JF 2).hom ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) jF 2).hom α)) = 0 :=
    (M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_res_ideles
        E M DM hactIM SL prH hprH prInfH hprInfH 1).1 _
      (M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp E F L M p hM DF DM hactIF hactIM
        SF ιF hιF SL ιL hιL JF hJF prG hprG prH hprH _ hdiv)
      (M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_infinitePlace_of_forall_eq_one E F M DF DM hactIF hactIM
        SF ιF hιF JF hJF SL prInfH hprInfH hinf _)

  set αM : groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ) 2 := (groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) iF 2).hom α with hαM
  rw [sqF α] at hz
  have hres : (groupCohomology.map SL.subtype (𝟙 (Rep.res SL.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ))) 2).hom αM = 0 :=
    (M4aHerbrand.map_two_res_units_ideles_injective_of_isPGroup E M p hM DM hactIM jM hjM).2 SL αM hz

  obtain ⟨αL, hαL⟩ := (IsGalois.map_two_units_injective_and_exists_of_map_subtype_eq_zero E L M hactL hactM SL ιL hιL iL hiL).2 αM hres
  exact ⟨αL, by rw [sqL αL, hαL, ← sqF α]⟩

end S_M4aHerbrand_exists_map_map_eq_map_map_of_dvd_natCard_decomp
end P2MW
export P2MW.S_M4aHerbrand_exists_map_map_eq_map_map_of_dvd_natCard_decomp (solution)
