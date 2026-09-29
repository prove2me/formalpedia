-- Prove2me | solution 1 for M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f9acddd9-e60d-524d-ba29-b94e52b82d76

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_CyclicCarry
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_M4aHerbrand_exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap
import Theorems.Thm_M4aHerbrand_prod_idelicArtinMap_single_eq_one
import Theorems.Thm_groupCohomology_exists_carry_H2pi_eq
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_eq_zero_of_isCyclic
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent groupCohomology
open HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)

    [MulDistribMulAction (F ≃ₐ[E] F) Fˣ]
    (hactF : ∀ (g : (F ≃ₐ[E] F)) (a : Fˣ), ((g • a : Fˣ) : F) = g (a : F))
    (j : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
    (hj : ∀ a : Fˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a))

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

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

  rename_i hprG hq hL'fd instSMA instMDA hΦ₁ hΦ₂ hΦ₃ hK₀fd hbase hθ hu' hn
  classical

  let A : Rep ℤ (F ≃ₐ[E] F) := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ
  have hw : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).under (𝓞 E) = v := fun v =>
    HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above E F v)

  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := F ≃ₐ[E] F)
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  have hfin : IsOfFinOrder s := isOfFinOrder_of_finite s
  haveI : IsMulCommutative (F ≃ₐ[E] F) := ⟨⟨fun x y => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hs x)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hs y)
    rw [← zpow_add, ← zpow_add, add_comm]⟩⟩

  obtain ⟨c, hcα⟩ : ∃ c : cocycles₂ A, (H2π A).hom c = α :=
    (ModuleCat.epi_iff_surjective (H2π A)).mp inferInstance α
  obtain ⟨hfixc, hcz, hcarry⟩ := groupCohomology.exists_carry_H2pi_eq s hs hfin c
  obtain ⟨a, ha⟩ : ∃ a : Eˣ, (Additive.ofMul (Units.map (algebraMap E F : E →* F) a) : A) = cyclicInv s ⇑c := by
    set b : Fˣ := Additive.toMul (cyclicInv s ⇑c) with hb
    have hsb : s • b = b := by
      have h := hfixc
      rw [show (cyclicInv s ⇑c : A) = Additive.ofMul b from rfl, Rep.ofMulDistribMulAction_ρ_apply_apply] at h
      exact Additive.ofMul.injective h
    have hgb : ∀ g : F ≃ₐ[E] F, g (b : F) = (b : F) := by
      intro g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hs g)
      have hmemst : s ^ k ∈ MulAction.stabilizer (F ≃ₐ[E] F) b :=
        Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.mpr hsb) k
      have hk : (s ^ k) • b = b := MulAction.mem_stabilizer_iff.mp hmemst
      rw [← hactF, hk]
    have hmem : (b : F) ∈ (⊥ : IntermediateField E F) := by
      rw [← IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField E F), IntermediateField.fixingSubgroup_bot]
      exact fun g => hgb g
    obtain ⟨e, he⟩ := IntermediateField.mem_bot.mp hmem
    have he0 : e ≠ 0 := by
      rintro rfl
      exact b.ne_zero (by rw [← he, map_zero])
    refine ⟨Units.mk0 e he0, ?_⟩
    rw [show (cyclicInv s ⇑c : A) = Additive.ofMul b from rfl]
    congr 1
    exact Units.ext he
  have hc : carryFun (A := A) s hs hfin (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)) ∈ cocycles₂ A := by
    rw [ha]; exact hcz
  have hαcarry : (H2π A).hom ⟨carryFun (A := A) s hs hfin (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)), hc⟩ = α := by
    rw [← hcα, ← hcarry]
    congr 1
    exact Subtype.ext (congrArg (carryFun (A := A) s hs hfin) ha)

  obtain ⟨𝔯, h𝔯, hram⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd E F
  obtain ⟨𝔣, h𝔯𝔣, hsupp, hadm⟩ :=
    LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E F 𝔯 h𝔯 hram (Module.finrank E F)
  obtain ⟨r, hr₁, hr₂, hr₃, hr₄⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank E F 𝔣 hadm

  have hxex : ∀ v : HeightOneSpectrum (𝓞 E), ∃ x : (AdeleRing (𝓞 E) E)ˣ,
      x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) ∧
      finPart v x = Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) a := by
    intro v
    have ha0 : algebraMap E (v.adicCompletion E) (a : E) ≠ 0 := (map_ne_zero _).mpr a.ne_zero
    let xf : RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
        (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletionIntegers E) Filter.cofinite :=
      RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletionIntegers E) v
        (algebraMap E (v.adicCompletion E) (a : E))
    let xf' : RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
        (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletionIntegers E) Filter.cofinite :=
      RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletionIntegers E) v
        (algebraMap E (v.adicCompletion E) (a : E))⁻¹
    have hff' : xf * xf' = 1 := by
      simp only [xf, xf']
      rw [← RestrictedProduct.mulSingle_mul, mul_inv_cancel₀ ha0, RestrictedProduct.mulSingle_one]
    have hf'f : xf' * xf = 1 := by rw [mul_comm]; exact hff'
    let xx : (AdeleRing (𝓞 E) E)ˣ :=
      ⟨((1 : InfiniteAdeleRing E), (xf : FiniteAdeleRing (𝓞 E) E)), ((1 : InfiniteAdeleRing E), (xf' : FiniteAdeleRing (𝓞 E) E)),
        Prod.ext (mul_one 1) hff', Prod.ext (mul_one 1) hf'f⟩
    refine ⟨xx, (M4aHerbrand.mem_idelesTrivialOn_iff _ _).mpr ⟨Units.ext rfl, fun w hw => Units.ext ?_⟩, Units.ext ?_⟩
    · rw [M4aHerbrand.coe_finPart_apply, Units.val_one]
      show xf w = 1
      exact RestrictedProduct.mulSingle_eq_of_ne _ _ (Set.mem_compl_singleton_iff.mp hw)
    · rw [M4aHerbrand.coe_finPart_apply, Units.coe_map]
      show xf v = algebraMap E (v.adicCompletion E) (a : E)
      exact RestrictedProduct.mulSingle_eq_same _ _ _
  choose x hx hxv using hxex

  have key : ∀ v : HeightOneSpectrum (𝓞 E), ∃ (nw : ℤ) (i : ℕ),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom
          ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom
            ((H2π A).hom ⟨carryFun (A := A) s hs hfin (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)), hc⟩)) =
        nw • (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)))) (θ v) 2).hom (u' v) ∧
      r (x v) = s ^ i ∧
      ((((nw : ℚ) / (Nat.card (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
        (((i : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
    intro v
    haveI : Fact (q v).Prime := hq v
    haveI : FiniteDimensional ℚ_[q v] (L' v) := hL'fd v
    letI : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v) := instSMA v
    letI : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ := instMDA v
    haveI : FiniteDimensional ℚ_[q v] (K₀ v) := hK₀fd v
    exact M4aHerbrand.exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap
      E F s hs hfin D hactI hactF j hj v (NumberField.PlaceAbove.above E F v) (hw v) (prG (NumberField.PlaceAbove.above E F v)) (hprG (NumberField.PlaceAbove.above E F v)) 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      a (x v) (hx v) (hxv v) hc (q v) (L' v) (Φ v) (hΦ₁ v) (hΦ₂ v) (hΦ₃ v) (K₀ v) (hbase v) (θ v) (hθ v) (u' v) (hu' v)
  choose nw i hcoord hri hquot using key

  have hnnw : ∀ v : HeightOneSpectrum (𝓞 E),
      ((((n v : ℚ) / (Nat.card (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
        ((((nw v : ℚ) / (Nat.card (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by
    intro v
    have h1 := hn v
    have h2 := hcoord v
    rw [hαcarry] at h2
    have h12 : (n v - nw v) • (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)))) (θ v) 2).hom (u' v) = 0 := by
      rw [sub_zsmul, ← h1, ← h2]
      simp
    have hdvd : (Nat.card (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℤ) ∣ (n v - nw v) := by

      haveI : Fact (q v).Prime := hq v
      haveI : FiniteDimensional ℚ_[q v] (L' v) := hL'fd v
      letI : MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (L' v) := instSMA v
      letI : MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (↥(L' v))ˣ := instMDA v
      haveI : FiniteDimensional ℚ_[q v] (K₀ v) := hK₀fd v
      haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) ((NumberField.PlaceAbove.above E F v).adicCompletion F) :=
        NumberField.PlaceDecomp.faithfulSMul_decomp E F (NumberField.PlaceAbove.above E F v)
      haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (L' v) := ⟨fun {g₁ g₂} h =>
        FaithfulSMul.eq_of_smul_eq_smul (α := (NumberField.PlaceAbove.above E F v).adicCompletion F) fun y =>
          (Φ v).injective (by rw [hΦ₃ v g₁ y, hΦ₃ v g₂ y]; exact h _)⟩
      have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) :=
        Group.isSolvable_of_comm (fun g₁ g₂ => Subtype.ext (mul_comm (g₁ : F ≃ₐ[E] F) (g₂ : F ≃ₐ[E] F)))
      obtain ⟨-, hcard, hspan⟩ :=
        ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
          (q v) (L' v) ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (hΦ₁ v) (hΦ₂ v) hsolv (K₀ v) (hbase v) (u' v) (hu' v)

      have hordu : ∀ m : ℤ, m • u' v = 0 → (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℤ) ∣ m := by
        intro m hm
        haveI : Fintype (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) := Fintype.ofFinite _
        have hc := hcard ⊤
        haveI : Finite ↥(groupCohomology (Rep.res (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (↥(L' v))ˣ)) 2) :=
          Nat.finite_of_card_ne_zero (by rw [hc]; exact Fintype.card_ne_zero)
        haveI : Fintype ↥(groupCohomology (Rep.res (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (↥(L' v))ˣ)) 2) := Fintype.ofFinite _
        set u₀ := (groupCohomology.map (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype (𝟙 (Rep.res (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (↥(L' v))ˣ))) 2).hom (u' v)
          with hu₀
        have hgen : ∀ y, y ∈ AddSubgroup.zmultiples u₀ := fun y => by
          have hy : y ∈ Submodule.span ℤ {u₀} := by rw [hspan ⊤]; trivial
          obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hy
          exact ⟨k, (int_smul_eq_zsmul _ k u₀).symm.trans hk⟩
        have hord : addOrderOf u₀ = Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) := by
          rw [addOrderOf_eq_card_of_forall_mem_zmultiples hgen, hc, ← Nat.card_eq_fintype_card, Subgroup.card_top]
        have hm0 : m • u₀ = 0 := by
          rw [hu₀, ← map_zsmul, hm, map_zero]
        rw [← hord]
        exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hm0

      have hinj : ∀ m : ℤ,
          m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v) = 0 → m • u' v = 0 := by

        let ΦM : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ →* (↥(L' v))ˣ := Units.map (Φ v).toRingHom.toMonoidHom
        have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (m : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ), ΦM (g • m) = g • ΦM m := by
          intro g m
          apply Units.ext
          rw [hΦ₂ v g (ΦM m)]
          show (Φ v) ((g • m : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)) = g • (Φ v) (m : ((NumberField.PlaceAbove.above E F v).adicCompletion F))
          rw [NumberField.PlaceDecomp.coe_smul_units, hΦ₃ v g]
        let θ' := M4aHerbrand.repHomOfMulEquivariant ΦM hΦM
        have hθθ' : θ v ≫ θ' = 𝟙 _ := by
          refine Rep.hom_ext ?_
          ext z
          rw [Rep.hom_comp, Rep.hom_id]
          show θ'.hom ((θ v).hom z) = z
          rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply]
          refine (congrArg Additive.ofMul ?_).trans (ofMul_toMul z)
          apply Units.ext
          show (Φ v) ((Additive.toMul ((θ v).hom z) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)) = ((Additive.toMul z : (↥(L' v))ˣ) : ↥(L' v))
          have h : ((Additive.toMul ((θ v).hom z) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)) = (Φ v).symm ((Additive.toMul z : (↥(L' v))ˣ) : ↥(L' v)) :=
            hθ v (Additive.toMul z)
          rw [h]
          exact (Φ v).apply_symm_apply _
        have hleft : ∀ y : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (↥(L' v))ˣ), (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) θ' 2).hom
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom y) = y := by
          intro y
          have hc := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp (θ v) θ' 2)
          simp only [hθθ', groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
            LinearMap.id_apply] at hc
          exact hc.symm
        intro m hm
        have h := congrArg ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) θ' 2).hom) hm
        rw [map_zsmul, map_zero, hleft] at h
        exact h
      exact hordu _ (hinj _ h12)
    obtain ⟨k, hk⟩ := hdvd
    have hN : (Nat.card (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℚ) ≠ 0 := by
      have h0 : 0 < Nat.card (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) := Nat.card_pos
      exact_mod_cast h0.ne'
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨k, ?_⟩
    rw [zsmul_one, ← sub_div, eq_div_iff hN]
    have hk' : ((n v : ℚ) - (nw v : ℚ)) =
        ((Nat.card (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℤ) : ℚ) * (k : ℚ) := by
      exact_mod_cast hk
    rw [hk']
    push_cast
    ring

  have hχ : ∃ χ : (F ≃ₐ[E] F) →* Multiplicative (AddCircle (1 : ℚ)),
      ∀ i : ℕ, χ (s ^ i) = Multiplicative.ofAdd ((((i : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by
    haveI : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
    haveI : Fintype (F ≃ₐ[E] F) := Fintype.ofFinite _
    have hord : orderOf (Multiplicative.ofAdd ((((1 : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) ∣ orderOf s := by
      rw [orderOf_ofAdd_eq_addOrderOf, AddCircle.addOrderOf_period_div Nat.card_pos,
        orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card]
    refine ⟨monoidHomOfForallMemZpowers hs hord, fun i => ?_⟩
    rw [map_pow, monoidHomOfForallMemZpowers_apply_gen, ← ofAdd_nsmul, ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div]
  obtain ⟨χ, hχ⟩ := hχ

  have hsummand : ∀ v : HeightOneSpectrum (𝓞 E),
      ((((n v : ℚ) / (Nat.card (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
        Multiplicative.toAdd (χ (r (x v))) := by
    intro v
    rw [hnnw v, hquot v, hri v, hχ (i v)]
    rfl
  obtain ⟨S, hS𝔣, hSa⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 E)),
      (∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣 → v ∈ S) ∧
      (∀ v : HeightOneSpectrum (𝓞 E), v ∉ S → (v.valuation E) (a : E) = 1) := by
    have hf𝔣 : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ 𝔣}.Finite := Ideal.finite_factors hadm.1
    have hfa : {v : HeightOneSpectrum (𝓞 E) | ¬ (v.valuation E) (a : E) = 1}.Finite := by
      refine ((IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 E) (a : E)).union
        (IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 E) ((a⁻¹ : Eˣ) : E))).subset ?_
      intro v hv
      simp only [Set.mem_setOf_eq] at hv
      simp only [Set.mem_union, IsDedekindDomain.HeightOneSpectrum.Support, Set.mem_setOf_eq]
      rcases lt_or_gt_of_ne hv with h | h
      · right
        have ha0 : 0 < (v.valuation E) (a : E) :=
          zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr a.ne_zero)
        rw [Units.val_inv_eq_inv_val, map_inv₀, one_lt_inv₀ ha0]
        exact h
      · left
        exact h
    refine ⟨(hf𝔣.union hfa).toFinset, fun v hv => ?_, fun v hv => ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq]
      exact Or.inl hv
    · by_contra h
      exact hv (by simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq]; exact Or.inr h)
  have hroff : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ S → r (x v) = 1 := by
    intro v hvS
    have hfin1 : ∀ v' : HeightOneSpectrum (𝓞 E), v' ≠ v →
        ((x v : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v' = 1 := by
      intro v' hv'
      have h := ((M4aHerbrand.mem_idelesTrivialOn_iff _ _).mp (hx v)).2 v' (Set.mem_compl_singleton_iff.mpr hv')
      have h' := congrArg (fun u : (v'.adicCompletion E)ˣ => (u : v'.adicCompletion E)) h
      simpa using h'
    have hinf1 : (x v : AdeleRing (𝓞 E) E).1 = 1 := by
      have h := ((M4aHerbrand.mem_idelesTrivialOn_iff _ _).mp (hx v)).1
      have h' := congrArg (fun u : (InfiniteAdeleRing E)ˣ => (u : InfiniteAdeleRing E)) h
      simpa using h'
    have hv1 : Valued.v (((x v : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v) = 1 := by
      have h := congrArg (fun u : (v.adicCompletion E)ˣ => (u : v.adicCompletion E)) (hxv v)
      simp only [M4aHerbrand.coe_finPart_apply, Units.coe_map, MonoidHom.coe_coe] at h
      rw [h]
      erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hSa v hvS
    have hadj : IsAdjuster E 𝔣 (x v) 1 := by
      have hsimp : x v * (Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) 1)⁻¹ = x v := by
        rw [map_one, inv_one, mul_one]
      refine ⟨fun v' hv' => ?_, fun τ => ?_⟩
      · have hne : v' ≠ v := fun h => hvS (h ▸ hS𝔣 v' hv')
        rw [hsimp, hfin1 v' hne, sub_self, map_one, map_zero]
        exact ⟨rfl, zero_le'⟩
      · rw [hsimp]
        exact archSign_of_fst_eq_one E τ hinf1
    rw [hr₄ (x v) hadj]
    refine finprod_eq_one_of_forall_eq_one fun v' => ?_
    have h0 : placeOrd E (projFin E (x v)) v' = 0 := by
      rw [placeOrd_eq_zero_iff]
      show Valued.v (((x v : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v') = 1
      rcases eq_or_ne v' v with rfl | hne
      · exact hv1
      · rw [hfin1 v' hne, map_one]
    rw [h0, zpow_zero]

  have hprod : ∏ v ∈ S, r (x v) = 1 :=
    M4aHerbrand.prod_idelicArtinMap_single_eq_one E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ hinf a x hx hxv S hS𝔣 hSa

  have hsupp : (Function.support fun v : HeightOneSpectrum (𝓞 E) =>
      ((((n v : ℚ) / (Nat.card (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) ⊆ S := by
    intro v hv
    by_contra hvS
    apply hv
    simp only [hsummand v, hroff v hvS, map_one, toAdd_one]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  simp_rw [hsummand]
  rw [← toAdd_prod, ← map_prod χ, hprod, map_one, toAdd_one]

end S_M4aHerbrand_finsum_div_natCard_decomp_eq_zero_of_isCyclic
end P2MW
export P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_eq_zero_of_isCyclic (solution)
