-- Prove2me | solution 1 for M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/edb544cc-9cd3-5220-8f87-720f5722ec78

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp
import Theorems.Thm_NumberField_exists_isGalois_compositum
import Theorems.Thm_M4aHerbrand_finsum_div_natCard_decomp_eq_zero_of_isCyclic
import Theorems.Thm_NumberField_PlaceDecomp_exists_forall_isLocalFundamentalClass_above
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
import Theorems.Thm_M4aHerbrand_finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower
import Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
import Theorems.Thm_NumberField_isPGroup_algEquiv_compositum_of_isPGroup
import Theorems.Thm_NumberField_PlaceDecomp_exists_eq_zsmul_map_of_isLocalFundamentalClass
import Theorems.Thm_M4aHerbrand_exists_map_map_eq_map_map_of_dvd_natCard_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_eq_zero_of_isPGroup
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_eq_zero_of_isPGroup.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart repHomOfMulEquivariant IdeleClassGroup IdeleGaloisDescent finsum_div_natCard_decomp_eq_zero_of_isCyclic exists_hom_res_decomp_ideles_adicCompletion_apply exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower GenuineDescent.genuineDescentDatum finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower exists_map_map_eq_map_map_of_dvd_natCard_decomp"
namespace ThmBP
p2m_open "M4aHerbrand"

theorem natCard_nsmul_eq_zero {G : Type} [Group G] [Finite G] (M : Rep ℤ G) (n : ℕ) (x : groupCohomology M (n + 1)) :
    Nat.card G • x = 0 := by
  obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul (⊥ : Subgroup G) M (n + 1)
  haveI := ModuleCat.subsingleton_of_isZero (isZero_groupCohomology_succ_of_subsingleton (Rep.res (⊥ : Subgroup G).subtype M) n)
  have h0 : (groupCohomology.map (⊥ : Subgroup G).subtype (𝟙 (Rep.res (⊥ : Subgroup G).subtype M)) (n + 1)).hom x = 0 :=
    Subsingleton.elim _ _
  rw [← Subgroup.index_bot, ← hcor x, h0, map_zero]

theorem coe_div_ne_zero_of_smul_ne_zero {A : Type} [AddCommGroup A] (d : ℕ) (hd : 0 < d) (m : ℤ) (y : A) (hy : d • y = 0)
    (h : m • y ≠ 0) : ((((m : ℚ) / (d : ℚ) : ℚ)) : AddCircle (1 : ℚ)) ≠ 0 := by
  intro h0
  rw [AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  rw [zsmul_eq_mul, mul_one] at hk
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hm : m = k * d := by
    have : (m : ℚ) = k * d := by rw [hk]; field_simp
    exact_mod_cast this
  apply h
  rw [hm, ← smul_smul, natCast_zsmul, hy, smul_zero]

end M4aHerbrand.ThmBP

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)

    [MulDistribMulAction (F ≃ₐ[E] F) Fˣ]
    (hactF : ∀ (g : (F ≃ₐ[E] F)) (a : Fˣ), ((g • a : Fˣ) : F) = g (a : F))
    (j : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
    (hj : ∀ a : Fˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a))

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))

    (α : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) 2))

    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
    (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
    (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
    (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
      ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L' v))
    (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))

    (n : HeightOneSpectrum (𝓞 E) → ℤ)
    (_ : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom α) =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) = 0 := by
  classical
  rename_i hprG hqF hfL' aL' auL' hQ hU hΦ hfK₀ hB hθ hu' hn

  by_cases hfin : (Function.support fun v : HeightOneSpectrum (𝓞 E) =>
      ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))).Finite
  swap
  · exact finsum_of_infinite_support hfin
  set T : Finset (HeightOneSpectrum (𝓞 E)) := hfin.toFinset with hT

  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hG

  obtain ⟨k, L, iFL, iNL, iAL, iGL, iCL, hcycL, hinfL, hdegL, hlocL, hpL⟩ :=
    NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp E T p a

  obtain ⟨M, iFM, iNM, iEM, iFMa, iLMa, iT1, iT2, hGalM, hgen⟩ := NumberField.exists_isGalois_compositum E F L
  haveI := hGalM

  have hpM : IsPGroup p (M ≃ₐ[E] M) := NumberField.isPGroup_algEquiv_compositum_of_isPGroup E F L M p hG hpL hgen

  let DL : IdeleGaloisDescent (𝓞 L) E L := M4aHerbrand.GenuineDescent.genuineDescentDatum E L
  let DM : IdeleGaloisDescent (𝓞 M) E M := M4aHerbrand.GenuineDescent.genuineDescentDatum E M
  letI instIL : MulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ := MulDistribMulAction.compHom _ DL.unitsAct
  letI instIM : MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ := MulDistribMulAction.compHom _ DM.unitsAct
  have hactIL : ∀ (g : (L ≃ₐ[E] L)) (x : (AdeleRing (𝓞 L) L)ˣ), g • x = DL.unitsAct g x := fun _ _ => rfl
  have hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x := fun _ _ => rfl
  letI instCF : MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F) := D.classMulDistribMulAction
  letI instCL : MulDistribMulAction (L ≃ₐ[E] L) (IdeleClassGroup (𝓞 L) L) := DL.classMulDistribMulAction
  letI instCM : MulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M) := DM.classMulDistribMulAction
  have hactCF : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c := fun _ _ => rfl
  have hactCL : ∀ (g : (L ≃ₐ[E] L)) (c : IdeleClassGroup (𝓞 L) L), g • c = DL.classAct g c := fun _ _ => rfl
  have hactCM : ∀ (g : (M ≃ₐ[E] M)) (c : IdeleClassGroup (𝓞 M) M), g • c = DM.classAct g c := fun _ _ => rfl
  letI instUL : MulDistribMulAction (L ≃ₐ[E] L) Lˣ := Units.mulDistribMulActionRight
  have hactL : ∀ (g : (L ≃ₐ[E] L)) (a : Lˣ), ((g • a : Lˣ) : L) = g (a : L) := fun _ _ => rfl

  let rF : (M ≃ₐ[E] M) →* (F ≃ₐ[E] F) := AlgEquiv.restrictNormalHom F
  let rL : (M ≃ₐ[E] M) →* (L ≃ₐ[E] L) := AlgEquiv.restrictNormalHom L
  have hrF : Function.Surjective rF := AlgEquiv.restrictNormalHom_surjective M
  have hrL : Function.Surjective rL := AlgEquiv.restrictNormalHom_surjective M
  let ιF : (M ≃ₐ[E] M) ⧸ rF.ker ≃* (F ≃ₐ[E] F) := QuotientGroup.quotientKerEquivOfSurjective rF hrF
  let ιL : (M ≃ₐ[E] M) ⧸ rL.ker ≃* (L ≃ₐ[E] L) := QuotientGroup.quotientKerEquivOfSurjective rL hrL
  have hιF : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ιF (QuotientGroup.mk g) x) = g (algebraMap F M x) := fun g x => by
    change algebraMap F M (QuotientGroup.kerLift rF (QuotientGroup.mk g) x) = _
    rw [QuotientGroup.kerLift_mk]
    exact AlgEquiv.restrictNormal_commutes g F x
  have hιL : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ιL (QuotientGroup.mk g) y) = g (algebraMap L M y) := fun g y => by
    change algebraMap L M (QuotientGroup.kerLift rL (QuotientGroup.mk g) y) = _
    rw [QuotientGroup.kerLift_mk]
    exact AlgEquiv.restrictNormal_commutes g L y

  obtain ⟨JF, jCF, hJF, -, -, -⟩ :=
    M4aHerbrand.exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
      E F M D DM hactI hactCF hactIM hactCM rF.ker ιF hιF
  obtain ⟨JL, jCL, hJL, -, -, -⟩ :=
    M4aHerbrand.exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
      E L M DL DM hactIL hactCL hactIM hactCM rL.ker ιL hιL

  obtain ⟨qM, hqM, LM, hfLM, aLM, auLM, ΦM, hQM, hUM, hΦM, KM, hfKM, hBM, θM, hθM, uM, huM⟩ :=
    NumberField.PlaceDecomp.exists_forall_isLocalFundamentalClass_above E M
  obtain ⟨qL, hqL, LL, hfLL, aLL, auLL, ΦL, hQL, hUL, hΦL, KL, hfKL, hBL, θL, hθL, uL, huL⟩ :=
    NumberField.PlaceDecomp.exists_forall_isLocalFundamentalClass_above E L
  obtain ⟨prM, hprM⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E M DM hactIM
  obtain ⟨prL, hprL⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E L DL hactIL

  let fL : Lˣ →* (AdeleRing (𝓞 L) L)ˣ := Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
  have hfL : ∀ (g : L ≃ₐ[E] L) (a : Lˣ), fL (g • a) = g • fL a := fun g a => by
    apply Units.ext
    change algebraMap L (AdeleRing (𝓞 L) L) (g (a : L)) = DL.act g (algebraMap L (AdeleRing (𝓞 L) L) (a : L))
    exact (DL.compat g (a : L)).symm
  let jL : Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ ⟶ Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ :=
    M4aHerbrand.repHomOfMulEquivariant fL hfL
  have hjL : ∀ a : Lˣ, jL.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a) :=
    fun a => rfl

  set x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2 :=
    (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom α with hx
  set xM : groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) 2 :=
    (groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' rF.ker)) JF 2).hom x with hxM
  have hsolvM : ∀ W : HeightOneSpectrum (𝓞 M), Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E M W) := fun W => by
    haveI := (hpM.to_subgroup (NumberField.PlaceDecomp.decomp E M W)).isNilpotent
    infer_instance
  have hsolvL : ∀ w : HeightOneSpectrum (𝓞 L), Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E L w) := fun w => by
    haveI := (hpL.to_subgroup (NumberField.PlaceDecomp.decomp E L w)).isNilpotent
    infer_instance
  have hreadM : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℤ,
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)).subtype
          (prM (NumberField.PlaceAbove.above E M v)) 2).hom xM =
        m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (θM v) 2).hom (uM v) :=
    fun v => by
      haveI := hqM v; haveI := hfLM v; letI := aLM v; letI := auLM v; haveI := hfKM v
      exact NumberField.PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass E M (NumberField.PlaceAbove.above E M v)
        (hsolvM _) (qM v) (LM v) (ΦM v) (hQM v) (hUM v) (hΦM v) (KM v) (hBM v) (θM v) (hθM v) (uM v) (huM v) _
  choose nM hnM using hreadM

  have e1 := M4aHerbrand.finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower
    E F M D DM hactI hactIM rF.ker ιF hιF JF hJF x prG hprG q hqF L' hfL' aL' auL' Φ hQ hU hΦ K₀ hfK₀ hB θ hθ u' hu' n hn
    prM hprM qM hqM LM hfLM aLM auLM ΦM hQM hUM hΦM KM hfKM hBM θM hθM uM huM nM hnM

  have hdiv : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype
          (prG (NumberField.PlaceAbove.above E F v)) 2).hom ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom α) ≠ 0 →
      ∀ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 E) = v → Nat.card (F ≃ₐ[E] F) ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E L w') := by
    intro v hne w' hw'
    rw [ha]
    refine hlocL v ?_ w' hw'
    rw [hT, Set.Finite.mem_toFinset, Function.mem_support]
    rw [hn v] at hne
    exact M4aHerbrand.ThmBP.coe_div_ne_zero_of_smul_ne_zero _ Nat.card_pos (n v) _
      (M4aHerbrand.ThmBP.natCard_nsmul_eq_zero _ 1 _) hne

  obtain ⟨αL, hαL⟩ := M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp E F L M p hpM D DL DM hactI hactIL hactIM
    hactF j hj hactL jL hjL rF.ker ιF hιF rL.ker ιL hιL JF hJF JL hJL prG hprG hinf α hdiv
  set yL : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ) 2 :=
    (groupCohomology.map (MonoidHom.id (L ≃ₐ[E] L)) jL 2).hom αL with hyL

  have hreadL : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℤ,
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E L (NumberField.PlaceAbove.above E L v)).subtype
          (prL (NumberField.PlaceAbove.above E L v)) 2).hom yL =
        m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E L (NumberField.PlaceAbove.above E L v))) (θL v) 2).hom (uL v) :=
    fun v => by
      haveI := hqL v; haveI := hfLL v; letI := aLL v; letI := auLL v; haveI := hfKL v
      exact NumberField.PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass E L (NumberField.PlaceAbove.above E L v)
        (hsolvL _) (qL v) (LL v) (ΦL v) (hQL v) (hUL v) (hΦL v) (KL v) (hBL v) (θL v) (hθL v) (uL v) (huL v) _
  choose nL hnL using hreadL

  have e3 := M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isCyclic E L DL hactIL hactL jL hjL hinfL αL prL hprL
    qL hqL LL hfLL aLL auLL ΦL hQL hUL hΦL KL hfKL hBL θL hθL uL huL nL hnL

  have hnM' : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)).subtype
          (prM (NumberField.PlaceAbove.above E M v)) 2).hom
          ((groupCohomology.map (ιL.toMonoidHom.comp (QuotientGroup.mk' rL.ker)) JL 2).hom yL) =
        nM v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (θM v) 2).hom (uM v) :=
    fun v => by rw [hyL, hαL]; exact hnM v
  have e2 := M4aHerbrand.finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower
    E L M DL DM hactIL hactIM rL.ker ιL hιL JL hJL yL prL hprL qL hqL LL hfLL aLL auLL ΦL hQL hUL hΦL KL hfKL hBL θL hθL uL huL nL hnL
    prM hprM qM hqM LM hfLM aLM auLM ΦM hQM hUM hΦM KM hfKM hBM θM hθM uM huM nM hnM'

  rw [← e1, e2, e3]

end S_M4aHerbrand_finsum_div_natCard_decomp_eq_zero_of_isPGroup
end P2MW
export P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_eq_zero_of_isPGroup (solution)
