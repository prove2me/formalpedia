-- Prove2me | solution 1 for NumberField.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e14ef0c9-2ecc-511c-b973-1166a84a3c25

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_KummerTheory_isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C
import Theorems.Thm_KummerTheory_natCard_algEquiv_eq_natCard_powerSubgroup_quotient
import Theorems.Thm_KummerTheory_powerSubgroup_eq_closure_sup_range_of_isSplittingField
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_inertia_eq_bot_of_pow_eq
import Theorems.Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom
import Theorems.Thm_NumberField_AdeleRing_relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow
import Theorems.Thm_NumberField_AdeleRing_principalIdeles_inf_unitIdelesOutside_eq_map_unit
import Theorems.Thm_NumberField_exists_pow_eq_of_forall_mem_range_powMonoidHom
import Theorems.Thm_M4aHerbrand_AdeleBaseChange_ideleBox_le_range_idelicNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero"

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped Polynomial

noncomputable section

namespace C3bAux

set_option linter.unusedSectionVars false

variable (E : Type) [Field E] [NumberField E]

theorem restrictNormalHom_mem_inertia_comap
    (F' : Type) [Field F'] [NumberField F'] [Algebra E F'] [IsGalois E F']
    (M : IntermediateField E F') [Normal E M]
    (w : HeightOneSpectrum (𝓞 F')) (σ : F' ≃ₐ[E] F') (hσ : σ ∈ w.asIdeal.inertia (F' ≃ₐ[E] F')) :
    AlgEquiv.restrictNormalHom M σ ∈ (w.asIdeal.comap (algebraMap (𝓞 M) (𝓞 F'))).inertia (M ≃ₐ[E] M) := by
  rw [Ideal.inertia, AddSubgroup.mem_inertia] at hσ ⊢
  intro x
  change (AlgEquiv.restrictNormalHom M σ) • x - x ∈ w.asIdeal.comap (algebraMap (𝓞 M) (𝓞 F'))
  rw [Ideal.mem_comap, map_sub]
  have key : algebraMap (𝓞 M) (𝓞 F') ((AlgEquiv.restrictNormalHom M σ) • x) = σ • algebraMap (𝓞 M) (𝓞 F') x := by
    apply Subtype.ext
    change algebraMap M F' ((σ.restrictNormal M) (x : M)) = σ (algebraMap M F' (x : M))
    exact AlgEquiv.restrictNormal_commutes σ M (x : M)
  rw [key]
  exact hσ _

theorem inertia_eq_bot_of_isSplittingField_prod {p : ℕ} (B : Finset Eˣ)
    (F' : Type) [Field F'] [NumberField F'] [Algebra E F'] [IsGalois E F']
    [Polynomial.IsSplittingField E F' (∏ u ∈ B, (Polynomial.X ^ p - Polynomial.C ((u : Eˣ) : E)))]
    (hcomm : ∀ σ τ : F' ≃ₐ[E] F', σ * τ = τ * σ)
    (v : HeightOneSpectrum (𝓞 E)) (hBv : ∀ u ∈ B, v.valuation E ((u : Eˣ) : E) = 1) (hpv : (p : 𝓞 E) ∉ v.asIdeal)
    (w : HeightOneSpectrum (𝓞 F')) (hw : w.asIdeal.under (𝓞 E) = v.asIdeal) :
    w.asIdeal.inertia (F' ≃ₐ[E] F') = ⊥ := by
  classical
  set f : E[X] := ∏ u ∈ B, (Polynomial.X ^ p - Polynomial.C ((u : Eˣ) : E)) with hf
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]

  suffices hroots : ∀ r ∈ f.rootSet F', σ r = r by
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ Algebra.adjoin E (f.rootSet F') := by
      rw [Polynomial.IsSplittingField.adjoin_rootSet]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem r hr => exact hroots r hr
    | algebraMap c => exact σ.commutes c
    | add x y _ _ hx hy => rw [map_add, hx, hy]; rfl
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]; rfl
  intro r hr

  obtain ⟨u, huB, hru⟩ : ∃ u ∈ B, r ^ p = algebraMap E F' ((u : Eˣ) : E) := by
    rw [Polynomial.mem_rootSet] at hr
    obtain ⟨-, hr⟩ := hr
    rw [hf, map_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨u, hu, h0⟩ := hr
    refine ⟨u, hu, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h0
    exact h0

  let M : IntermediateField E F' := IntermediateField.adjoin E {r}
  haveI : (M.fixingSubgroup).Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  haveI : IsGalois E M := by
    rw [← IsGalois.fixedField_fixingSubgroup M]; infer_instance

  have hrint : IsIntegral E r := IsIntegral.of_finite E r
  let α : M := IntermediateField.AdjoinSimple.gen E r
  have hα : α ^ p = algebraMap E M ((u : Eˣ) : E) := by
    apply Subtype.ext
    change r ^ p = algebraMap E F' ((u : Eˣ) : E)
    exact hru
  have hgen : ∀ τ : M ≃ₐ[E] M, τ α = α → τ = 1 := by
    intro τ hτ
    have hpb : (IntermediateField.adjoin.powerBasis hrint).gen = α := IntermediateField.adjoin.powerBasis_gen hrint
    have h := (IntermediateField.adjoin.powerBasis hrint).algHom_ext (f := (τ : M →ₐ[E] M)) (g := AlgHom.id E M)
      (by rw [hpb]; (first | exact hτ | simpa using hτ | (have h__ := hτ; simp at h__; exact h__)))
    exact AlgEquiv.ext fun x => by simpa using congrArg (fun φ : M →ₐ[E] M => φ x) h

  let wM : HeightOneSpectrum (𝓞 M) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 M) (𝓞 F'))
      isPrime := Ideal.IsPrime.comap _
      ne_bot := by
        intro h0
        apply v.ne_bot
        rw [← hw]
        have : (w.asIdeal.comap (algebraMap (𝓞 M) (𝓞 F'))).comap (algebraMap (𝓞 E) (𝓞 M)) = ⊥ := by
          rw [h0, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)]
        rwa [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq] at this }
  have hwMv : wM.under (𝓞 E) = v := by
    apply HeightOneSpectrum.ext
    change (w.asIdeal.comap (algebraMap (𝓞 M) (𝓞 F'))).comap (algebraMap (𝓞 E) (𝓞 M)) = v.asIdeal
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact hw

  have key := IsDedekindDomain.HeightOneSpectrum.Extension.inertia_eq_bot_of_pow_eq E M ((u : Eˣ) : E) α hα hgen v
    (hBv u huB) (by exact_mod_cast hpv) ⟨wM, hwMv⟩

  have hres := restrictNormalHom_mem_inertia_comap E F' M w σ hσ
  change AlgEquiv.restrictNormalHom M σ ∈ wM.asIdeal.inertia (M ≃ₐ[E] M) at hres
  rw [key, Subgroup.mem_bot] at hres
  exact (AlgEquiv.restrictNormal_eq_one_iff M σ).1 hres r (IntermediateField.mem_adjoin_simple_self E r)

section boxes

variable {E}
variable (S' : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ)

abbrev Box : Subgroup (AdeleRing (𝓞 E) E)ˣ :=
  NumberField.AdeleRing.ideleBox (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E)))
    (fun v => (powMonoidHom p : (v.adicCompletion E)ˣ →* (v.adicCompletion E)ˣ).range)
    (fun w => (powMonoidHom p : (w.Completion)ˣ →* (w.Completion)ˣ).range)

theorem pow_mem_box {j : (AdeleRing (𝓞 E) E)ˣ}
    (hj : j ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E)))) :
    j ^ p ∈ Box S' p := by
  have hjp : j ^ p ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) := pow_mem hj p
  rw [NumberField.AdeleRing.mem_ideleBox_iff]
  refine ⟨⟨fun v _ => ⟨NumberField.AdeleRing.finiteUnitsComponent (𝓞 E) E v j, by rw [powMonoidHom_apply, map_pow]⟩,
    fun v hv => hjp v hv⟩, fun w => ⟨NumberField.AdeleRing.infiniteUnitsComponent (𝓞 E) E w j, by rw [powMonoidHom_apply, map_pow]⟩⟩

theorem unitIdelesTrivialOn_le_box :
    unitIdelesTrivialOn (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) ≤ Box S' p := by
  intro x hx
  obtain ⟨hxU, hxinf, hxT⟩ := (mem_unitIdelesTrivialOn_iff (↑S' : Set (HeightOneSpectrum (𝓞 E))) x).mp hx
  rw [NumberField.AdeleRing.mem_ideleBox_iff]
  refine ⟨⟨fun v hv => ?_, fun v hv => hxU v hv⟩, fun w => ?_⟩
  · have h1 : NumberField.AdeleRing.finiteUnitsComponent (𝓞 E) E v x = 1 := by
      ext
      rw [NumberField.AdeleRing.val_finiteUnitsComponent, Units.val_one, ← coe_finPart_apply, hxT v hv, Units.val_one]
    rw [h1]; exact one_mem _
  · have h1 : NumberField.AdeleRing.infiniteUnitsComponent (𝓞 E) E w x = 1 := by
      ext
      rw [NumberField.AdeleRing.val_infiniteUnitsComponent, Units.val_one, ← coe_infPart_apply, hxinf, Units.val_one]
      rfl
    rw [h1]; exact one_mem _

theorem box_le_range_pow_sup_unitIdelesTrivialOn :
    Box S' p ≤ (powMonoidHom p : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ).range
      ⊔ unitIdelesTrivialOn (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) := by
  classical
  intro x hx
  obtain ⟨⟨hS, hoff⟩, hinf⟩ := (NumberField.AdeleRing.mem_ideleBox_iff _ _ _ x).mp hx

  choose yf hyf using fun v : {v // v ∈ S'} => (hS v.1 (by exact_mod_cast v.2))
  choose yi hyi using hinf

  let af : FiniteAdeleRing (𝓞 E) E :=
    RestrictedProduct.mk (fun v => if h : v ∈ S' then ((yf ⟨v, h⟩ : (v.adicCompletion E)ˣ) : v.adicCompletion E) else 1)
      (Filter.eventually_cofinite.2 ((S' : Set (HeightOneSpectrum (𝓞 E))).toFinite.subset fun v hv => by
        by_contra hvS
        have hvS' : v ∉ S' := fun h => hvS (Finset.mem_coe.2 h)
        apply hv
        show (if h : v ∈ S' then _ else _) ∈ (v.adicCompletionIntegers E : Set (v.adicCompletion E))
        rw [dif_neg hvS']
        exact SetLike.mem_coe.2 (one_mem _)))
  let bf : FiniteAdeleRing (𝓞 E) E :=
    RestrictedProduct.mk (fun v => if h : v ∈ S' then (((yf ⟨v, h⟩)⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) else 1)
      (Filter.eventually_cofinite.2 ((S' : Set (HeightOneSpectrum (𝓞 E))).toFinite.subset fun v hv => by
        by_contra hvS
        have hvS' : v ∉ S' := fun h => hvS (Finset.mem_coe.2 h)
        apply hv
        show (if h : v ∈ S' then _ else _) ∈ (v.adicCompletionIntegers E : Set (v.adicCompletion E))
        rw [dif_neg hvS']
        exact SetLike.mem_coe.2 (one_mem _)))
  have haf : ∀ v, af v = if h : v ∈ S' then ((yf ⟨v, h⟩ : (v.adicCompletion E)ˣ) : v.adicCompletion E) else 1 := fun v => rfl
  have hbf : ∀ v, bf v = if h : v ∈ S' then (((yf ⟨v, h⟩)⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) else 1 := fun v => rfl
  have hab : af * bf = 1 := by
    refine FiniteAdeleRing.ext _ fun v => ?_
    change af v * bf v = 1
    rw [haf, hbf]
    split_ifs with h
    · rw [Units.mul_inv]
    · rw [one_mul]
  let y : (AdeleRing (𝓞 E) E)ˣ :=
    ⟨(fun w => (yi w : w.Completion), af), (fun w => ((yi w)⁻¹ : (w.Completion)ˣ), bf),
      Prod.ext (funext fun w => Units.mul_inv _) hab,
      Prod.ext (funext fun w => Units.inv_mul _) (by rw [mul_comm] at hab; exact hab)⟩
  have hyinf : ∀ w, NumberField.AdeleRing.infiniteUnitsComponent (𝓞 E) E w y = yi w := fun w => Units.ext rfl
  have hyS : ∀ v (h : v ∈ S'), NumberField.AdeleRing.finiteUnitsComponent (𝓞 E) E v y = yf ⟨v, h⟩ := fun v h =>
    Units.ext (by rw [NumberField.AdeleRing.val_finiteUnitsComponent]; change af v = _; rw [haf, dif_pos h])
  have hyoff : ∀ v, v ∉ S' → NumberField.AdeleRing.finiteUnitsComponent (𝓞 E) E v y = 1 := fun v h =>
    Units.ext (by rw [NumberField.AdeleRing.val_finiteUnitsComponent, Units.val_one]; change af v = _; rw [haf, dif_neg h])

  set z := x * (y ^ p)⁻¹ with hz
  have hzU : z ∈ unitIdelesTrivialOn (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) := by
    refine (mem_unitIdelesTrivialOn_iff _ z).2 ⟨fun v hv => ?_, ?_, fun v hv => ?_⟩
    · have hvS : v ∉ S' := by exact_mod_cast hv
      have e1 : NumberField.AdeleRing.finiteUnitsComponent (𝓞 E) E v z = NumberField.AdeleRing.finiteUnitsComponent (𝓞 E) E v x := by
        rw [hz, map_mul, map_inv, map_pow, hyoff v hvS, one_pow, inv_one, mul_one]
      constructor
      · rw [← NumberField.AdeleRing.val_finiteUnitsComponent, e1, NumberField.AdeleRing.val_finiteUnitsComponent]
        exact (hoff v hv).1
      · rw [← NumberField.AdeleRing.val_finiteUnitsComponent, map_inv, e1, ← map_inv,
          NumberField.AdeleRing.val_finiteUnitsComponent]
        exact (hoff v hv).2
    · refine Units.ext (funext fun w => ?_)
      rw [coe_infPart_apply, Units.val_one]
      change ((z : AdeleRing (𝓞 E) E).1) w = 1
      rw [← NumberField.AdeleRing.val_infiniteUnitsComponent, hz, map_mul, map_inv, map_pow, hyinf, ← hyi w,
        powMonoidHom_apply, mul_inv_cancel, Units.val_one]
    · have hvS : v ∈ S' := by exact_mod_cast hv
      refine Units.ext ?_
      rw [coe_finPart_apply, Units.val_one, ← NumberField.AdeleRing.val_finiteUnitsComponent, hz, map_mul, map_inv, map_pow,
        hyS v hvS, ← hyf ⟨v, hvS⟩, powMonoidHom_apply, mul_inv_cancel, Units.val_one]
  have hx' : x = y ^ p * z := by rw [hz, mul_comm x, mul_inv_cancel_left]
  rw [hx']
  exact Subgroup.mul_mem_sup ⟨y, rfl⟩ hzU

theorem principalIdeles_sup_pow_sup_unitIdelesTrivialOn_eq
    (hS : principalIdeles (𝓞 E) E ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) = ⊤) :
    principalIdeles (𝓞 E) E
        ⊔ (powMonoidHom p : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ).range
        ⊔ unitIdelesTrivialOn (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E)))
      = principalIdeles (𝓞 E) E ⊔ Box S' p := by
  apply le_antisymm
  · refine sup_le (sup_le le_sup_left ?_) (le_trans (unitIdelesTrivialOn_le_box S' p) le_sup_right)
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ principalIdeles (𝓞 E) E ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E ↑S' := by rw [hS]; trivial
    obtain ⟨e, he, j, hj, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [powMonoidHom_apply, mul_pow]
    exact Subgroup.mul_mem_sup (pow_mem he p) (pow_mem_box S' p hj)
  · refine sup_le (le_sup_left.trans le_sup_left) ?_
    exact (box_le_range_pow_sup_unitIdelesTrivialOn S' p).trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)

end boxes

theorem index_sup_mul_relIndex_inf_eq_relIndex {G : Type*} [CommGroup G] (P J Box : Subgroup G)
    (hPJ : P ⊔ J = ⊤) (hBJ : Box ≤ J) :
    (P ⊔ Box).index * (P ⊓ Box).relIndex (P ⊓ J) = Box.relIndex J := by

  have h1 : (P ⊔ Box).index = (Box ⊔ P ⊓ J).relIndex J := by
    have htop : (P ⊔ Box) ⊔ J = ⊤ := by
      rw [sup_assoc, sup_eq_right.mpr hBJ, hPJ]
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right]
    congr 1

    apply le_antisymm
    · rintro x ⟨hx, hxJ⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
      have haJ : a ∈ J := by
        have := J.mul_mem hxJ (J.inv_mem (hBJ hb))
        rwa [mul_inv_cancel_right] at this
      exact Subgroup.mem_sup.mpr ⟨b, hb, a, ⟨ha, haJ⟩, mul_comm b a⟩
    · exact sup_le (fun x hx => ⟨Subgroup.mem_sup_right hx, hBJ hx⟩) (fun x hx => ⟨Subgroup.mem_sup_left hx.1, hx.2⟩)

  have h2 : Box.relIndex (Box ⊔ P ⊓ J) = (P ⊓ Box).relIndex (P ⊓ J) := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right]
    congr 1
    ext x; simp only [Subgroup.mem_inf]; tauto
  rw [h1, ← h2, mul_comm]
  exact Subgroup.relIndex_mul_relIndex Box (Box ⊔ P ⊓ J) J le_sup_left (sup_le hBJ inf_le_right)

section partiii

variable {E}
variable {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p E).Nonempty)
  (S' : Finset (HeightOneSpectrum (𝓞 E)))
  (hSp : ∀ v : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ v.asIdeal → v ∈ S')
  (hS : principalIdeles (𝓞 E) E ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) = ⊤)

abbrev ιE : Eˣ →* (AdeleRing (𝓞 E) E)ˣ :=
  Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E)

theorem ιE_injective : Function.Injective (ιE (E := E)) := by
  intro a b h
  exact Units.ext (NumberField.AdeleRing.algebraMap_injective (𝓞 E) E (congrArg (fun u : (AdeleRing (𝓞 E) E)ˣ => (u : AdeleRing (𝓞 E) E)) h))

include hp hζ hSp hS in

theorem principalIdeles_inf_box_eq :
    principalIdeles (𝓞 E) E ⊓ Box S' p
      = (((powMonoidHom p : ↥((↑S' : Set (HeightOneSpectrum (𝓞 E))).unit E) →* _).range).map
          ((↑S' : Set (HeightOneSpectrum (𝓞 E))).unit E).subtype).map ιE := by
  classical
  have hPJ := NumberField.AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E)))
  apply le_antisymm
  · intro x hx
    have hxJ : x ∈ principalIdeles (𝓞 E) E ⊓ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E ↑S' :=
      ⟨hx.1, NumberField.AdeleRing.ideleBox_le_unitIdelesOutside _ _ _ _ _ hx.2⟩
    rw [hPJ] at hxJ
    obtain ⟨u, hu, rfl⟩ := hxJ

    obtain ⟨⟨hbS, -⟩, hbinf⟩ := (NumberField.AdeleRing.mem_ideleBox_iff _ _ _ _).mp hx.2
    obtain ⟨c, hc⟩ := NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom E hp hζ S' ∅ hSp hS
      (fun _ _ => ⟨1, fun v _ => by simp, fun v hv => absurd hv (Finset.notMem_empty v)⟩)
      ((u : Eˣ) : E) (fun v hv _ => hu v (by exact_mod_cast hv))
      (fun v hv => by
        obtain ⟨y, hy⟩ := hbS v (by exact_mod_cast hv)
        refine ⟨(y : v.adicCompletion E), ?_⟩
        have := congrArg (fun z : (v.adicCompletion E)ˣ => (z : v.adicCompletion E)) hy
        simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, NumberField.AdeleRing.val_finiteUnitsComponent] at this
        rw [this]
        rfl)
      (fun w _ => by
        obtain ⟨y, hy⟩ := hbinf w
        refine ⟨(y : w.Completion), ?_⟩
        have := congrArg (fun z : (w.Completion)ˣ => (z : w.Completion)) hy
        simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, NumberField.AdeleRing.val_infiniteUnitsComponent] at this
        rw [this]
        rfl)

    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hc
      exact u.ne_zero hc
    let cu : Eˣ := Units.mk0 c hc0
    have hcu : u = cu ^ p := Units.ext (by (first | exact hc | simpa using hc | (have h__ := hc; simp at h__; exact h__)))
    have hcS : cu ∈ (↑S' : Set (HeightOneSpectrum (𝓞 E))).unit E := by
      intro v hv
      have h1 : v.valuation E ((u : Eˣ) : E) = 1 := hu v hv
      rw [hcu, Units.val_pow_eq_pow_val, map_pow] at h1
      rcases lt_trichotomy (v.valuation E (cu : E)) 1 with h | h | h
      · exact absurd h1 (ne_of_lt (pow_lt_one₀ zero_le' h hp.ne_zero))
      · exact h
      · exact absurd h1 (ne_of_gt (one_lt_pow₀ h hp.ne_zero))
    refine ⟨cu ^ p, ⟨⟨cu ^ p, ?_⟩, ⟨⟨⟨cu, hcS⟩, rfl⟩, rfl⟩⟩, by rw [hcu]⟩
    exact pow_mem hcS p
  · rintro _ ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩
    simp only [powMonoidHom_apply, Subgroup.coe_subtype, map_pow]
    have hcJ : ιE (c : Eˣ) ∈ principalIdeles (𝓞 E) E ⊓ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E ↑S' := by
      rw [hPJ]; exact ⟨c, c.2, rfl⟩
    exact ⟨pow_mem hcJ.1 p, pow_mem_box S' p hcJ.2⟩

include hp hζ hSp hS in
theorem relIndex_principalIdeles_inf_box :
    (principalIdeles (𝓞 E) E ⊓ Box S' p).relIndex
      (principalIdeles (𝓞 E) E ⊓ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))))
      = p ^ (S'.card + NumberField.Units.rank E + 1) := by
  rw [principalIdeles_inf_box_eq hp hζ S' hSp hS,
    NumberField.AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E)))]

  rw [Subgroup.relIndex_map_map_of_injective _ _ ιE_injective, Subgroup.relIndex, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _), Subgroup.index]
  have h := NumberField.natCard_sUnit_quotient_range_powMonoidHom E (↑S' : Set (HeightOneSpectrum (𝓞 E))) hζ (n := p)
  have hS'card : Nat.card (↥(↑S' : Set (HeightOneSpectrum (𝓞 E)))) = S'.card := by
    simp only [Finset.coe_sort_coe, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hS'card] at h
  exact h

theorem card_infinitePlace_eq_rank_add_one : Fintype.card (InfinitePlace E) = NumberField.Units.rank E + 1 := by
  rw [NumberField.Units.rank, Nat.sub_add_cancel Fintype.card_pos]

include hp hζ hSp hS in

theorem index_principalIdeles_sup_pow_sup_unitIdelesTrivialOn :
    (principalIdeles (𝓞 E) E
        ⊔ (powMonoidHom p : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ).range
        ⊔ unitIdelesTrivialOn (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E)))).index
      = p ^ (S'.card + NumberField.Units.rank E + 1) := by
  rw [principalIdeles_sup_pow_sup_unitIdelesTrivialOn_eq S' p hS]
  have key := index_sup_mul_relIndex_inf_eq_relIndex (principalIdeles (𝓞 E) E)
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E)))) (Box S' p) hS
    (NumberField.AdeleRing.ideleBox_le_unitIdelesOutside _ _ _ _ _)
  rw [relIndex_principalIdeles_inf_box hp hζ S' hSp hS,
    NumberField.AdeleRing.relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow hp hζ S' hSp,
    card_infinitePlace_eq_rank_add_one] at key
  have h2 : 2 * (S'.card + (NumberField.Units.rank E + 1))
      = (S'.card + NumberField.Units.rank E + 1) + (S'.card + NumberField.Units.rank E + 1) := by omega
  rw [h2, pow_add p (S'.card + NumberField.Units.rank E + 1) (S'.card + NumberField.Units.rank E + 1)] at key
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) key

end partiii

theorem range_powMonoidHom_subgroupOf_unit (S : Set (HeightOneSpectrum (𝓞 E))) {p : ℕ} (hp : 0 < p) :
    ((powMonoidHom p : Eˣ →* Eˣ).range).subgroupOf (S.unit E) = (powMonoidHom p : ↥(S.unit E) →* ↥(S.unit E)).range := by
  ext ⟨u, hu⟩
  simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨c, hc⟩
    have hcS : c ∈ S.unit E := by
      intro v hv
      have h1 : v.valuation E ((u : Eˣ) : E) = 1 := hu v hv
      rw [← hc, Units.val_pow_eq_pow_val, map_pow] at h1
      rcases lt_trichotomy (v.valuation E (c : E)) 1 with h | h | h
      · exact absurd h1 (ne_of_lt (pow_lt_one₀ zero_le' h hp.ne'))
      · exact h
      · exact absurd h1 (ne_of_gt (one_lt_pow₀ h hp.ne'))
    exact ⟨⟨c, hcS⟩, Subtype.ext hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, congrArg Subtype.val hc⟩

theorem natCard_quotient_subgroupOf_congr {G : Type*} [Group G] {H H' : Subgroup G} (N : Subgroup G) (h : H = H') :
    Nat.card (H ⧸ N.subgroupOf H) = Nat.card (H' ⧸ N.subgroupOf H') := by
  subst h; rfl

end C3bAux

open C3bAux in
theorem solution
    (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p E).Nonempty)
    (S' : Finset (HeightOneSpectrum (𝓞 E)))
    (hSp : ∀ v : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ v.asIdeal → v ∈ S')
    (hS : principalIdeles (𝓞 E) E ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) = ⊤) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra E F') (_ : IsGalois E F'),
      (∀ σ τ : F' ≃ₐ[E] F', σ * τ = τ * σ) ∧ (∀ σ : F' ≃ₐ[E] F', σ ^ p = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 E), v ∉ S' → ∀ w : HeightOneSpectrum (𝓞 F'),
        w.asIdeal.under (𝓞 E) = v.asIdeal → w.asIdeal.inertia (F' ≃ₐ[E] F') = ⊥) ∧
      principalIdeles (𝓞 E) E ⊔ ((genuineBaseChange E F').idelicNorm).range
        = principalIdeles (𝓞 E) E
            ⊔ (powMonoidHom p : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ).range
            ⊔ unitIdelesTrivialOn (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  set Ugrp : Subgroup Eˣ := (↑S' : Set (HeightOneSpectrum (𝓞 E))).unit E with hUgrp
  have hcardU : Nat.card (Ugrp ⧸ (powMonoidHom p : Ugrp →* Ugrp).range) = p ^ (S'.card + NumberField.Units.rank E + 1) := by
    have h := NumberField.natCard_sUnit_quotient_range_powMonoidHom E (↑S' : Set (HeightOneSpectrum (𝓞 E))) hζ
    have hS'card : Nat.card (↥(↑S' : Set (HeightOneSpectrum (𝓞 E)))) = S'.card := by
      simp only [Finset.coe_sort_coe, Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [hS'card] at h
    exact h
  haveI hfinQ : Finite (Ugrp ⧸ (powMonoidHom p : Ugrp →* Ugrp).range) :=
    Nat.finite_of_card_ne_zero (by rw [hcardU]; exact pow_ne_zero _ hp.ne_zero)
  letI : Fintype (Ugrp ⧸ (powMonoidHom p : Ugrp →* Ugrp).range) := Fintype.ofFinite _
  let B : Finset Eˣ := Finset.univ.image fun q : Ugrp ⧸ (powMonoidHom p : Ugrp →* Ugrp).range => ((Quotient.out q : Ugrp) : Eˣ)
  have hBU : ∀ b ∈ B, b ∈ Ugrp := by
    intro b hb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact (Quotient.out q).2
  have hBgen : Ugrp ≤ Subgroup.closure (B : Set Eˣ) ⊔ (powMonoidHom p : Eˣ →* Eˣ).range := by
    intro u hu
    let q : Ugrp ⧸ (powMonoidHom p : Ugrp →* Ugrp).range := QuotientGroup.mk ⟨u, hu⟩
    have hq : (Quotient.out q : Ugrp)⁻¹ * ⟨u, hu⟩ ∈ (powMonoidHom p : Ugrp →* Ugrp).range := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    obtain ⟨c, hc⟩ := hq
    have hu' : u = ((Quotient.out q : Ugrp) : Eˣ) * ((c : Ugrp) : Eˣ) ^ p := by
      have := congrArg (fun z : Ugrp => (z : Eˣ)) hc
      simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at this
      rw [this, mul_inv_cancel_left]
    rw [hu']
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure ?_)) (Subgroup.mem_sup_right ⟨(c : Ugrp), rfl⟩)
    exact Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩

  let f : E[X] := ∏ u ∈ B, (Polynomial.X ^ p - Polynomial.C ((u : Eˣ) : E))
  let F' : Type := f.SplittingField
  haveI : NumberField F' := NumberField.of_module_finite E F'
  obtain ⟨hgal, hcomm, hexp⟩ :=
    KummerTheory.isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C E F' hζ B
  haveI := hgal
  haveI : IsMulCommutative (F' ≃ₐ[E] F') := ⟨⟨hcomm⟩⟩

  have hunr : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ S' → ∀ w : HeightOneSpectrum (𝓞 F'),
      w.asIdeal.under (𝓞 E) = v.asIdeal → w.asIdeal.inertia (F' ≃ₐ[E] F') = ⊥ := by
    intro v hv w hw
    refine inertia_eq_bot_of_isSplittingField_prod E B F' hcomm v (fun u hu => ?_) (fun h => hv (hSp v h)) w hw
    exact hBU u hu v (by exact_mod_cast hv)

  have hS'ne : (∏ v ∈ S', v.asIdeal : Ideal (𝓞 E)) ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
    push Not
    intro v _
    rw [Ideal.zero_eq_bot]
    exact v.ne_bot
  have hram : ∀ v : HeightOneSpectrum (𝓞 E), (primeAbove E F' v).inertia (F' ≃ₐ[E] F') ≠ ⊥ →
      v.asIdeal ∣ ∏ v ∈ S', v.asIdeal := by
    intro v hv
    by_contra hdvd
    have hvS' : v ∉ S' := fun h => hdvd (Finset.dvd_prod_of_mem _ h)
    apply hv
    let w : HeightOneSpectrum (𝓞 F') := ⟨primeAbove E F' v, (primeAbove_isMaximal E F' v).isPrime, primeAbove_ne_bot E F' v⟩
    exact hunr v hvS' w (under_primeAbove E F' v)
  obtain ⟨𝔣, -, -, hadm⟩ := LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E F'
    (∏ v ∈ S', v.asIdeal) hS'ne hram (Module.finrank E F')
  obtain ⟨r, -, hr₂, hr₃, -⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
      E F' 𝔣 hadm

  have hUT : unitIdelesTrivialOn (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) ≤ ((genuineBaseChange E F').idelicNorm).range := by
    refine le_trans ?_ (M4aHerbrand.AdeleBaseChange.ideleBox_le_range_idelicNorm E F' (genuineBaseChange E F')
      (dvd_refl (Module.finrank E F')) S' (fun _ => ⊥) (fun _ => ⊥)
      (fun v _ => Or.inl bot_le) (fun v hv w => ?_) (fun w _ => bot_le))
    · intro x hx
      obtain ⟨hxU, hxinf, hxT⟩ := (mem_unitIdelesTrivialOn_iff (↑S' : Set (HeightOneSpectrum (𝓞 E))) x).mp hx
      rw [NumberField.AdeleRing.mem_ideleBox_iff]
      refine ⟨⟨fun v hv => ?_, fun v hv => hxU v hv⟩, fun w => ?_⟩
      · rw [Subgroup.mem_bot]
        ext
        rw [NumberField.AdeleRing.val_finiteUnitsComponent, Units.val_one, ← coe_finPart_apply, hxT v hv, Units.val_one]
      · rw [Subgroup.mem_bot]
        ext
        rw [NumberField.AdeleRing.val_infiniteUnitsComponent, Units.val_one, ← coe_infPart_apply, hxinf, Units.val_one]
        rfl
    · exact hunr v hv w.1 (by have := w.2; simpa using congrArg HeightOneSpectrum.asIdeal this)
  have hsub : principalIdeles (𝓞 E) E
        ⊔ (powMonoidHom p : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ).range
        ⊔ unitIdelesTrivialOn (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E)))
      ≤ principalIdeles (𝓞 E) E ⊔ ((genuineBaseChange E F').idelicNorm).range := by
    refine sup_le (sup_le le_sup_left ?_) (le_trans hUT le_sup_right)
    rintro _ ⟨y, rfl⟩
    rw [← hr₂, MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hexp]

  set N : ℕ := S'.card + NumberField.Units.rank E + 1 with hN
  have hidxA : (principalIdeles (𝓞 E) E ⊔ ((genuineBaseChange E F').idelicNorm).range).index = p ^ N := by
    rw [← hr₂, Subgroup.index_ker, MonoidHom.range_eq_top.2 hr₃, Subgroup.card_top]

    rw [KummerTheory.natCard_algEquiv_eq_natCard_powerSubgroup_quotient E F' hζ hcomm hexp]
    have hPS : groupCohomology.Kummer.powerSubgroup E F' p = Ugrp ⊔ (powMonoidHom p : Eˣ →* Eˣ).range := by
      rw [KummerTheory.powerSubgroup_eq_closure_sup_range_of_isSplittingField E F' hζ B]
      apply le_antisymm
      · exact sup_le_sup_right ((Subgroup.closure_le _).2 fun b hb => hBU b hb) _
      · exact sup_le hBgen le_sup_right
    rw [natCard_quotient_subgroupOf_congr _ hPS,
      ← Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient Ugrp (powMonoidHom p : Eˣ →* Eˣ).range).toEquiv,
      range_powMonoidHom_subgroupOf_unit E _ hp.pos, hcardU]

  have hidxB := index_principalIdeles_sup_pow_sup_unitIdelesTrivialOn hp hζ S' hSp hS

  refine ⟨F', inferInstance, inferInstance, inferInstance, hgal, hcomm, hexp, hunr, ?_⟩
  refine le_antisymm ?_ hsub
  have hmul := Subgroup.relIndex_mul_index hsub
  rw [hidxA, hidxB, ← hN] at hmul
  have hone : (principalIdeles (𝓞 E) E
        ⊔ (powMonoidHom p : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ).range
        ⊔ unitIdelesTrivialOn (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E)))).relIndex
        (principalIdeles (𝓞 E) E ⊔ ((genuineBaseChange E F').idelicNorm).range) = 1 := by
    have hpN : p ^ N ≠ 0 := pow_ne_zero _ hp.ne_zero
    exact (mul_left_eq_self₀.1 hmul).resolve_right hpN
  exact Subgroup.relIndex_eq_one.1 hone

end
end S_NumberField_exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top
end P2MW
export P2MW.S_NumberField_exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top (solution)
