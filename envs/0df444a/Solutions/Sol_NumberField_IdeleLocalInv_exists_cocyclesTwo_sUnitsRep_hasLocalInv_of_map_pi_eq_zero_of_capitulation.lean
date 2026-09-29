-- Prove2me | solution 1 for NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0ac31f27-a1e5-5346-b1d0-61a8615861d3

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_IdeleLocalInvariant

import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_IdeleLocalInv_exists_zsmul_eq_zero_and_map_eq_of_map_pi_eq_zero
import Theorems.Thm_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation
import Theorems.Thm_NumberField_IdeleLocalInv_hasLocalInv_map_genuineBaseChange
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation
p2m_attr_erase "instance" "groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl groupCohomology.locTotal₂S_apply groupCohomology.continuousH2ToH2_mk groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π groupCohomology.locTotal_apply groupCohomology.totalPairing_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open M4aHerbrand.GenuineDescent
open scoped NumberField.PlaceDecomp

theorem solution
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K] [IsGalois E K'']
    (S : Finset (HeightOneSpectrum (𝓞 E)))

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K)]
    (hact : ∀ (g : K ≃ₐ[E] K) (c : IdeleClassGroup (𝓞 K) K), g • c = D.classAct g c)
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))
    (π : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K))
    (hπ : ∀ y : (AdeleRing (𝓞 K) K)ˣ, π.hom (Additive.ofMul y) = Additive.ofMul (QuotientGroup.mk y : IdeleClassGroup (𝓞 K) K))

    (D'' : IdeleGaloisDescent (𝓞 K'') E K'')
    [MulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ]
    (hactI'' : ∀ (g : K'' ≃ₐ[E] K'') (x : (AdeleRing (𝓞 K'') K'')ˣ), g • x = D''.unitsAct g x)
    (j'' : NumberField.SUnits.sUnitsRep E K'' S ⟶ Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ)
    (hj'' : ∀ y, Additive.toMul (j''.hom y) =
      Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') (NumberField.SUnits.val E K'' S y))

    (p : ℕ) [Fact p.Prime]
    (hcap : ∀ (I : Ideal (𝓞 K)) (k : ℕ) (a : 𝓞 K), a ≠ 0 → I ^ p ^ k = Ideal.span {a} →
      (I.map (algebraMap (𝓞 K) (𝓞 K''))).IsPrincipal)

    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (k : ℕ) (hx : (p ^ k : ℤ) • x = 0)
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 K), (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom x = 0)
    (hπx : (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) π 2).hom x = 0) :
    ∃ (f : cocycles₂ (NumberField.SUnits.sUnitsRep E K'' S)) (k' : ℕ),
      (p ^ k' : ℤ) • (H2π _ f) = 0 ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (t : AddCircle (1 : ℚ)),
        NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t →
        NumberField.IdeleLocalInv.HasLocalInv E K'' D'' hactI'' ((groupCohomology.map (MonoidHom.id (K'' ≃ₐ[E] K'')) j'' 2) (H2π _ f)) v t := by
  classical
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K

  letI instF : MulDistribMulAction (K ≃ₐ[E] K) Kˣ :=
    { smul := fun g a => Units.map ((g : K ≃ₐ[E] K) : K →* K) a
      one_smul := fun a => Units.ext rfl
      mul_smul := fun g₁ g₂ a => Units.ext rfl
      smul_one := fun g => Units.ext (map_one (g : K ≃ₐ[E] K))
      smul_mul := fun g a b => Units.ext (map_mul (g : K ≃ₐ[E] K) (a : K) (b : K)) }
  have hactF : ∀ (g : (K ≃ₐ[E] K)) (a : Kˣ), ((g • a : Kˣ) : K) = g (a : K) := fun g a => rfl
  obtain ⟨j, hj⟩ : ∃ j : (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) ⟶ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ),
      ∀ a : Kˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
    refine ⟨M4aHerbrand.repHomOfMulEquivariant (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) (fun g a => ?_), fun a => rfl⟩
    apply Units.ext
    rw [hactI]
    show algebraMap K (AdeleRing (𝓞 K) K) ((g • a : Kˣ) : K) = D.act g (algebraMap K (AdeleRing (𝓞 K) K) (a : K))
    rw [hactF, D.compat]

  obtain ⟨y, k₁, hy, hjy⟩ :=
    NumberField.IdeleLocalInv.exists_zsmul_eq_zero_and_map_eq_of_map_pi_eq_zero E K D hactI hact hactF j hj π hπ p x k hx hπx

  obtain ⟨incl, hincl⟩ : ∃ incl : Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) ⟶ Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') K''ˣ,
      ∀ a : Kˣ, incl.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K K'' : K →* K'') a) := by
    let fι : Kˣ →* K''ˣ := Units.map (algebraMap K K'' : K →* K'')
    have hfι : ∀ (σ : (K'' ≃ₐ[E] K'')) (a : Kˣ), fι ((AlgEquiv.restrictNormalHom K σ) • a) = σ • fι a := by
      intro σ a
      apply Units.ext
      show algebraMap K K'' (((AlgEquiv.restrictNormalHom K σ) • a : Kˣ) : K) = σ (algebraMap K K'' (a : K))
      rw [hactF]
      exact AlgEquiv.restrictNormal_commutes σ K (a : K)
    refine ⟨Rep.ofHom ⟨(MonoidHom.toAdditive fι).toIntLinearMap, fun σ => LinearMap.ext fun z => ?_⟩, fun a => rfl⟩
    change Additive.ofMul (fι ((AlgEquiv.restrictNormalHom K σ) • (Additive.toMul z : Kˣ))) = Additive.ofMul (σ • fι (Additive.toMul z : Kˣ))
    rw [hfι]

  have hsupp' : ∀ w : HeightOneSpectrum (𝓞 K), (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom
        ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) j 2).hom y) = 0 := by
    intro w hw; rw [hjy]; exact hsupp w hw
  obtain ⟨f, k', hf, hιf⟩ :=
    NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation
      E K K'' S D hactI prG hprG hactF j hj incl hincl p hcap y k₁ hy hsupp'
  refine ⟨f, k', hf, fun v t h => ?_⟩

  obtain ⟨J, hJ⟩ : ∃ J : Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶ (Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ),
      ∀ z : (AdeleRing (𝓞 K) K)ˣ, Additive.toMul (J.hom (Additive.ofMul z)) = Units.map (genuineBaseChange K K'').β.toMonoidHom z := by
    let fJ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K'') K'')ˣ := Units.map (genuineBaseChange K K'').β.toMonoidHom
    have hfJ : ∀ (σ : (K'' ≃ₐ[E] K'')) (z : (AdeleRing (𝓞 K) K)ˣ), fJ ((AlgEquiv.restrictNormalHom K σ) • z) = σ • fJ z := by
      intro σ z
      rw [hactI, hactI'']
      exact (M4aHerbrand.IdeleGaloisDescent.unitsAct_map_genuineBaseChange E K K'' D D'' σ z).symm
    refine ⟨Rep.ofHom ⟨(MonoidHom.toAdditive fJ).toIntLinearMap, fun σ => LinearMap.ext fun z => ?_⟩, fun z => rfl⟩
    change Additive.ofMul (fJ ((AlgEquiv.restrictNormalHom K σ) • (Additive.toMul z : (AdeleRing (𝓞 K) K)ˣ))) = Additive.ofMul (σ • fJ (Additive.toMul z : (AdeleRing (𝓞 K) K)ˣ))
    rw [hfJ]

  have hsq : (groupCohomology.map (MonoidHom.id (K'' ≃ₐ[E] K'')) j'' 2) (H2π _ f) =
      (groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) J 2).hom x := by

    obtain ⟨jK'', hjK''⟩ : ∃ jK'' : Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') K''ˣ ⟶ (Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ),
        ∀ a : K''ˣ, jK''.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') a) := by
      refine ⟨M4aHerbrand.repHomOfMulEquivariant (Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'')) (fun g a => ?_), fun a => rfl⟩
      apply Units.ext
      rw [hactI'']
      show algebraMap K'' (AdeleRing (𝓞 K'') K'') (g (a : K'')) = D''.act g (algebraMap K'' (AdeleRing (𝓞 K'') K'') (a : K''))
      exact (D''.compat g (a : K'')).symm
    have hj''fac : j'' = NumberField.SUnits.toUnitsRep E K'' S ≫ jK'' := by
      refine Rep.hom_ext ?_
      ext y
      show j''.hom y = jK''.hom ((NumberField.SUnits.toUnitsRep E K'' S).hom y)
      rw [← ofMul_toMul (j''.hom y), hj'',
        show (NumberField.SUnits.toUnitsRep E K'' S).hom y = Additive.ofMul (NumberField.SUnits.val E K'' S y) from rfl]
      exact (hjK'' (NumberField.SUnits.val E K'' S y)).symm
    have hsq1 : incl ≫ jK'' = (Rep.resFunctor (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K))).map j ≫ J := by
      refine Rep.hom_ext ?_
      ext z
      show jK''.hom (incl.hom z) = J.hom (j.hom z)
      have h1 : incl.hom z = Additive.ofMul (Units.map (algebraMap K K'' : K →* K'') (Additive.toMul z)) := hincl (Additive.toMul z)
      have h2 : j.hom z = Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Additive.toMul z)) := hj (Additive.toMul z)
      have e1 : Additive.toMul (jK''.hom (incl.hom z)) =
          Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') (Units.map (algebraMap K K'' : K →* K'') (Additive.toMul z)) := by
        rw [h1]; exact congrArg Additive.toMul (hjK'' _)
      have e2 : Additive.toMul (J.hom (j.hom z)) =
          Units.map (genuineBaseChange K K'').β.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Additive.toMul z)) := by
        rw [h2]; exact hJ _
      have e3 : Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') (Units.map (algebraMap K K'' : K →* K'') (Additive.toMul z)) =
          Units.map (genuineBaseChange K K'').β.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Additive.toMul z)) :=
        Units.ext ((genuineBaseChange K K'').β_compat ((Additive.toMul z : Kˣ) : K)).symm
      exact Additive.toMul.injective (e1.trans (e3.trans e2.symm))
    have hU1 : groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) incl 2 ≫ groupCohomology.map (MonoidHom.id (K'' ≃ₐ[E] K'')) jK'' 2 =
        groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) (incl ≫ jK'') 2 :=
      (groupCohomology.map_comp (A := (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ)) (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) (MonoidHom.id (K'' ≃ₐ[E] K'')) incl jK'' 2).symm
    have hU2 : groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) j 2 ≫ groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) J 2 =
        groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) ((Rep.resFunctor (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K))).map j ≫ J) 2 :=
      (groupCohomology.map_comp (A := (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ)) (MonoidHom.id (K ≃ₐ[E] K)) (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) j J 2).symm
    show (groupCohomology.map (MonoidHom.id (K'' ≃ₐ[E] K'')) j'' 2).hom (H2π _ f) = _
    rw [hj''fac, groupCohomology.map_id_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hιf, ← hjy,
      ← LinearMap.comp_apply, ← ModuleCat.hom_comp, hU1, hsq1, ← hU2, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hsq]
  exact NumberField.IdeleLocalInv.hasLocalInv_map_genuineBaseChange E K K'' D hactI D'' hactI'' J hJ x v t h

end S_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation
end P2MW
export P2MW.S_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation (solution)
