-- Prove2me | solution 1 for M4aHerbrand.exists_adeleBaseChange_invariant_groupCohomology_ideleClassGroup_map_eq_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/02f722f6-a12e-55ac-ace9-afe03d940cfc

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_FiniteConorm
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Theorems.Thm_groupCohomology_exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top
import Theorems.Thm_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
import Theorems.Thm_NumberField_AdeleRing_mem_unitIdelesOutside_iff_forall_valued_snd_eq_one
import Theorems.Thm_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_Bridge_genuineBeta_comp_of_tower
import Theorems.Thm_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_adeleBaseChange_invariant_groupCohomology_ideleClassGroup_map_eq_of_invariant
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal Rep.relationCarrier.instAddCommGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_adeleBaseChange_invariant_groupCohomology_ideleClassGroup_map_eq_of_invariant.M4aHerbrand"
open scoped NumberField.PlaceDecomp
open scoped TensorProduct

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_infPart_apply coe_finPart_apply IdeleClassGroup IdeleGaloisDescent Bridge.genuineβ Bridge.genuineβ_fst Bridge.genuineβ_snd Bridge.continuous_genuineβ Bridge.genuineβ_compat Bridge.finiteConorm Bridge.finiteConorm_apply GenuineDescent.genuineDescentDatum GenuineDescent.genuineDescentDatum_act actOf actOf_algebraMap Bridge.genuineTensorEquiv Bridge.genuineTensorEquiv_one_tmul Bridge.genuineTensorEquiv_tmul_one exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower Bridge.valued_finiteConorm_apply_and_finprod_pow_eq subsingleton_ideleGaloisDescent Bridge.genuineBeta_comp_of_tower exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two"
namespace BaseChangeAux
p2m_open "M4aHerbrand"

theorem finPart_map_genuineβ (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']
    (z : (AdeleRing (𝓞 F) F)ˣ) (w' : HeightOneSpectrum (𝓞 F')) :
    ((finPart w' (Units.map ((M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) : (w'.adicCompletion F')ˣ) : w'.adicCompletion F') =
      HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨w', rfl⟩ : (w'.under (𝓞 F)).Extension (𝓞 F'))
        ((finPart (w'.under (𝓞 F)) z : ((w'.under (𝓞 F)).adicCompletion F)ˣ) : (w'.under (𝓞 F)).adicCompletion F) := by
  rw [coe_finPart_apply, Units.coe_map, MonoidHom.coe_coe, M4aHerbrand.Bridge.genuineβ_snd, M4aHerbrand.Bridge.finiteConorm_apply,
    coe_finPart_apply]

theorem a_loc (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F'] :
    ∀ (z z' : (AdeleRing (𝓞 F) F)ˣ) (w' : HeightOneSpectrum (𝓞 F')),
      finPart (w'.under (𝓞 F)) z = finPart (w'.under (𝓞 F)) z' →
      finPart w' (Units.map ((M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) =
        finPart w' (Units.map ((M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z') := by
  intro z z' w' h
  apply Units.ext
  rw [finPart_map_genuineβ E F F', finPart_map_genuineβ E F F', h]

theorem under_under_eq (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] (w' : HeightOneSpectrum (𝓞 F')) :
    (w'.under (𝓞 F)).under (𝓞 E) = w'.under (𝓞 E) :=
  HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal,
    Ideal.under_under])

theorem a_out (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F'] :
    ∀ (T : Set (HeightOneSpectrum (𝓞 E))) (z : (AdeleRing (𝓞 F) F)ˣ),
      (∀ w : HeightOneSpectrum (𝓞 F), w.under (𝓞 E) ∉ T → finPart w z = 1) →
      ∀ w' : HeightOneSpectrum (𝓞 F'), w'.under (𝓞 E) ∉ T →
        finPart w' (Units.map ((M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) = 1 := by
  intro T z hz w' hw'
  apply Units.ext
  rw [finPart_map_genuineβ E F F', hz (w'.under (𝓞 F)) (by rw [under_under_eq E F F']; exact hw'), Units.val_one, map_one, Units.val_one]

theorem a_inf (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F'] :
    ∀ z : (AdeleRing (𝓞 F) F)ˣ, infPart z = 1 → infPart (Units.map ((M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) = 1 := by
  intro z hz
  apply Units.ext
  rw [coe_infPart_apply, Units.coe_map, MonoidHom.coe_coe, M4aHerbrand.Bridge.genuineβ_fst, ← coe_infPart_apply, hz, Units.val_one,
    map_one, Units.val_one]

theorem exists_classHom (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c) :
    ∃ (j : Rep.res (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶ Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')),
      ((∀ x : (AdeleRing (𝓞 F) F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) =
          Additive.ofMul (QuotientGroup.mk (Units.map ((M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') x) : IdeleClassGroup (𝓞 F') F')) ∧
        Function.Injective j.hom ∧
        (∀ c' : Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'), (∀ g' : F' ≃ₐ[E] F', g' ∈ (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker →
            (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')).ρ g' c' = c') → c' ∈ Set.range j.hom)) := by

  letI instIF : MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ := MulDistribMulAction.compHom _ D.unitsAct
  letI instIF' : MulDistribMulAction (F' ≃ₐ[E] F') (AdeleRing (𝓞 F') F')ˣ := MulDistribMulAction.compHom _ D'.unitsAct
  have hπs : Function.Surjective (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := F) (E := F')
  obtain ⟨J, j, -, hj, hjinj, hjim⟩ :=
    M4aHerbrand.exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower E F F' D D'
      (fun _ _ => rfl) hact (fun _ _ => rfl) hact' (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker (QuotientGroup.quotientKerEquivOfSurjective _ hπs)
      (fun g x => by
        change algebraMap F F' ((AlgEquiv.restrictNormalHom F g) x) = g (algebraMap F F' x)
        rw [show AlgEquiv.restrictNormalHom F g = g.restrictNormal F from rfl, AlgEquiv.restrictNormal_commutes])
  refine ⟨j, fun x => hj x, hjinj, fun c' hc' => ?_⟩
  exact (hjim (Additive.toMul c')).2 (fun s hs => by
    have h := hc' s hs
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply] at h
    exact congrArg Additive.toMul h)

theorem actOf_algebraMap_base {R E S F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E] [IsFractionRing R E]
    [NumberField E] [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F] [IsFractionRing S F] [NumberField F] [Algebra E F]
    [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) (σ : F ≃ₐ[E] F) (a : AdeleRing R E) :
    actOf R E S F te σ (algebraMap (AdeleRing R E) (AdeleRing S F) a) = algebraMap (AdeleRing R E) (AdeleRing S F) a :=
  (te.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans te)).commutes a

theorem actOf_te_tmul {R E S F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E] [IsFractionRing R E]
    [NumberField E] [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F] [IsFractionRing S F] [NumberField F] [Algebra E F]
    [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) (σ : F ≃ₐ[E] F) (a : AdeleRing R E) (f : F) :
    actOf R E S F te σ (te (a ⊗ₜ[E] f)) = te (a ⊗ₜ[E] σ f) := by
  show te ((Algebra.TensorProduct.congr AlgEquiv.refl σ) (te.symm (te (a ⊗ₜ[E] f)))) = _
  rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

theorem genuineβ_act
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']
    (D : IdeleGaloisDescent (𝓞 F) E F) (D' : IdeleGaloisDescent (𝓞 F') E F')
    (g' : F' ≃ₐ[E] F') (x : AdeleRing (𝓞 F) F) :
    M4aHerbrand.Bridge.genuineβ F F' (D.act (AlgEquiv.restrictNormalHom F g') x) =
      D'.act g' (M4aHerbrand.Bridge.genuineβ F F' x) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F') E F'
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum E F := Subsingleton.elim _ _
  obtain rfl : D' = M4aHerbrand.GenuineDescent.genuineDescentDatum E F' := Subsingleton.elim _ _
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act, M4aHerbrand.GenuineDescent.genuineDescentDatum_act]
  letI algF := (M4aHerbrand.Bridge.genuineβ E F).toAlgebra
  letI algF' := (M4aHerbrand.Bridge.genuineβ E F').toAlgebra
  set σ := AlgEquiv.restrictNormalHom F g' with hσ

  obtain ⟨t, rfl⟩ := (M4aHerbrand.Bridge.genuineTensorEquiv E F).surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul a f =>
    rw [actOf_te_tmul]

    have hte : ∀ f₀ : F, M4aHerbrand.Bridge.genuineTensorEquiv E F (a ⊗ₜ[E] f₀) =
        M4aHerbrand.Bridge.genuineβ E F a * algebraMap F (AdeleRing (𝓞 F) F) f₀ := by
      intro f₀
      have : a ⊗ₜ[E] f₀ = (a ⊗ₜ[E] (1 : F)) * ((1 : AdeleRing (𝓞 E) E) ⊗ₜ[E] f₀) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul, M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one, M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul]
    rw [hte, hte, map_mul, map_mul, M4aHerbrand.Bridge.genuineβ_compat]

    have htow : M4aHerbrand.Bridge.genuineβ F F' (M4aHerbrand.Bridge.genuineβ E F a) = M4aHerbrand.Bridge.genuineβ E F' a := by
      rw [← M4aHerbrand.Bridge.genuineBeta_comp_of_tower E F F']; rfl
    rw [htow, M4aHerbrand.Bridge.genuineβ_compat]

    rw [map_mul]
    have h1 : actOf (𝓞 E) E (𝓞 F') F' (M4aHerbrand.Bridge.genuineTensorEquiv E F') g' (M4aHerbrand.Bridge.genuineβ E F' a) =
        M4aHerbrand.Bridge.genuineβ E F' a :=
      actOf_algebraMap_base (M4aHerbrand.Bridge.genuineTensorEquiv E F') g' a
    have h2 : actOf (𝓞 E) E (𝓞 F') F' (M4aHerbrand.Bridge.genuineTensorEquiv E F') g' (algebraMap F' (AdeleRing (𝓞 F') F') (algebraMap F F' f)) =
        algebraMap F' (AdeleRing (𝓞 F') F') (g' (algebraMap F F' f)) :=
      actOf_algebraMap (𝓞 E) E (𝓞 F') F' _ (M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul E F') g' _
    rw [h1, h2]
    congr 2

    rw [hσ]
    exact AlgEquiv.restrictNormal_commutes g' F f

theorem unitIdelesOutside_map_genuineβ
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F']
    (T : Set (HeightOneSpectrum (𝓞 E))) (z : (AdeleRing (𝓞 F) F)ˣ)
    (hz : z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F {w | w.under (𝓞 E) ∈ T}) :
    Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 F') F' {w' | w'.under (𝓞 E) ∈ T} := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one] at hz ⊢
  intro w' hw'
  have hw : w'.under (𝓞 F) ∉ {w : HeightOneSpectrum (𝓞 F) | w.under (𝓞 E) ∈ T} := by
    simpa only [Set.mem_setOf_eq, under_under_eq E F F'] using hw'
  have key := (M4aHerbrand.Bridge.valued_finiteConorm_apply_and_finprod_pow_eq (𝓞 F) F F' (𝓞 F')
    (Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom z)).1 w'
  have e : (((Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z :
        (AdeleRing (𝓞 F') F')ˣ) : AdeleRing (𝓞 F') F').2 : FiniteAdeleRing (𝓞 F') F') w' =
      ((Units.map (M4aHerbrand.Bridge.finiteConorm (𝓞 F) F F' (𝓞 F')).toMonoidHom
        (Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom z) :
          (FiniteAdeleRing (𝓞 F') F')ˣ) : FiniteAdeleRing (𝓞 F') F') w' := rfl
  have hz' : Valued.v ((↑(Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom z) :
      FiniteAdeleRing (𝓞 F) F) (w'.under (𝓞 F))) = 1 := by exact hz _ hw
  rw [e, key, hz', one_pow]

private theorem _root_.M4aHerbrand.BaseChangeAux.basechange
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']

    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))

    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 F'), (w.adicCompletion F')ˣ →* (AdeleRing (𝓞 F') F')ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F'), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)
    (lam' : ∀ w : HeightOneSpectrum (𝓞 F'),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))
    (hlam' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      (lam' w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' w x) : IdeleClassGroup (𝓞 F') F')) :
    ∃ (j : Rep.res (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶ Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')),
      (let J : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F' := M4aHerbrand.Bridge.genuineβ F F'
       (Continuous J ∧
        (∀ a : F, J (algebraMap F (AdeleRing (𝓞 F) F) a) = algebraMap F' (AdeleRing (𝓞 F') F') (algebraMap F F' a)) ∧
        (∀ (g' : F' ≃ₐ[E] F') (x : AdeleRing (𝓞 F) F), J (D.act (AlgEquiv.restrictNormalHom F g') x) = D'.act g' (J x)) ∧

        (∀ (T : Set (HeightOneSpectrum (𝓞 E))) (z : (AdeleRing (𝓞 F) F)ˣ),
          (∀ w : HeightOneSpectrum (𝓞 F), w.under (𝓞 E) ∉ T → finPart w z = 1) →
          ∀ w' : HeightOneSpectrum (𝓞 F'), w'.under (𝓞 E) ∉ T →
            finPart w' (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) = 1) ∧

        (∀ (T : Set (HeightOneSpectrum (𝓞 E))) (z : (AdeleRing (𝓞 F) F)ˣ),
          z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F {w | w.under (𝓞 E) ∈ T} →
          Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z ∈
            NumberField.AdeleRing.unitIdelesOutside (𝓞 F') F' {w' | w'.under (𝓞 E) ∈ T}) ∧

        (∀ z : (AdeleRing (𝓞 F) F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) = 1) ∧

        (∀ (z z' : (AdeleRing (𝓞 F) F)ˣ) (w' : HeightOneSpectrum (𝓞 F')),
          finPart (w'.under (𝓞 F)) z = finPart (w'.under (𝓞 F)) z' →
          finPart w' (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) =
            finPart w' (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z'))) ∧
      ((∀ x : (AdeleRing (𝓞 F) F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) =
          Additive.ofMul (QuotientGroup.mk (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') x) : IdeleClassGroup (𝓞 F') F')) ∧
        Function.Injective j.hom ∧
        (∀ c' : Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'), (∀ g' : F' ≃ₐ[E] F', g' ∈ (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker →
            (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')).ρ g' c' = c') → c' ∈ Set.range j.hom))) := by
  obtain ⟨j, hb⟩ := exists_classHom E F F' D hact D' hact'
  refine ⟨j, ?_, hb⟩
  refine ⟨M4aHerbrand.Bridge.continuous_genuineβ F F', fun a => M4aHerbrand.Bridge.genuineβ_compat F F' a,
    fun g' x => genuineβ_act E F F' D D' g' x, a_out E F F', fun T z hz => unitIdelesOutside_map_genuineβ E F F' T z hz,
    a_inf E F F', a_loc E F F'⟩

p2m_export "M4aHerbrand.BaseChangeAux" "basechange"
end M4aHerbrand.BaseChangeAux

namespace InvInflAux

private theorem index_nsmul_one_div_card {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    H.index • ((((1 : ℚ) / (Nat.card G : ℚ) : ℚ)) : AddCircle (1 : ℚ)) =
      (((1 : ℚ) / (Nat.card ↥H : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← AddCircle.coe_nsmul]
  congr 1
  have hG : (Nat.card G : ℚ) = (Nat.card ↥H : ℚ) * (H.index : ℚ) := by
    rw [← H.card_mul_index]; push_cast; ring
  have hH : (Nat.card ↥H : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := ↥H)).ne'
  have hi : (H.index : ℚ) ≠ 0 := by exact_mod_cast H.index_ne_zero_of_finite
  rw [hG, nsmul_eq_mul]
  field_simp

private theorem nsmul_one_div_mul {k n : ℕ} (hk : k ≠ 0) (hn : n ≠ 0) :
    n • ((((1 : ℚ) / ((k * n : ℕ) : ℚ) : ℚ)) : AddCircle (1 : ℚ)) = (((1 : ℚ) / (k : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← AddCircle.coe_nsmul]
  congr 1
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [nsmul_eq_mul]; push_cast; field_simp

private theorem addMonoidHom_map_int_smul {M N : Type} [AddCommGroup M] [AddCommGroup N] (instM : Module ℤ M) (instN : Module ℤ N)
    (f : M →+ N) (k : ℤ) (x : M) :
    f (@HSMul.hSMul ℤ M M (@instHSMul ℤ M instM.toSMul) k x) = @HSMul.hSMul ℤ N N (@instHSMul ℤ N instN.toSMul) k (f x) := by
  have hM : instM = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  have hN : instN = AddCommGroup.toIntModule N := Subsingleton.elim _ _
  subst hM; subst hN
  exact map_zsmul f k x

private theorem exists_eq_zsmul_one_div_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0) (t : AddCircle (1 : ℚ)) (h : n • t = 0) :
    ∃ z : ℤ, t = z • ((((1 : ℚ) / (n : ℚ) : ℚ)) : AddCircle (1 : ℚ)) := by
  induction t using QuotientAddGroup.induction_on with
  | H r =>
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨z, ?_⟩
    rw [← AddCircle.coe_zsmul]
    congr 1
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    rw [zsmul_eq_mul, nsmul_eq_mul] at hz
    rw [zsmul_eq_mul, mul_one_div, eq_div_iff hn', mul_comm]
    linarith

private theorem invsys_of_fc
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))
    (uF : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)
    (hcard : ∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S)
    (hspan : ∀ S : Subgroup (F ≃ₐ[E] F), Submodule.span ℤ
        {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom uF} = ⊤)
    (hloc : ∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)),
        m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u') =
          m • (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom uF) :
    ∃ (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ))
      (inv : ∀ H : Subgroup (F ≃ₐ[E] F), ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ AddCircle (1 : ℚ)),

      Function.Injective invG ∧ (∀ H : Subgroup (F ≃ₐ[E] F), Function.Injective (inv H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0) ∧
      (∀ (H : Subgroup (F ≃ₐ[E] F)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F)) (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
        inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) = H.index • invG x) ∧

      (∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)),
        m • inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F))
        (cor : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
        (∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2),
          cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) = H.index • x) →
        ∀ y : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2), invG (cor y) = inv H y) ∧
      invG uF = (((1 : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  classical
  letI : Fintype (F ≃ₐ[E] F) := Fintype.ofFinite _
  obtain ⟨invG, inv, hinjG, hinj, himG, him, hres, huG, huH⟩ :=
    groupCohomology.exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) uF
      (fun S _ => hcard S) hspan
  refine ⟨invG, inv, hinjG, hinj, himG, him, hres, ?_, ?_, huG⟩
  · intro w q _ L' _ _ _ Φ h1 h2 h3 K₀ _ hB θ hθ u' hu' m a hm hma
    rw [← map_nsmul, hloc w q L' Φ h1 h2 h3 K₀ hB θ hθ u' hu' m a hm hma, map_nsmul, huH, ← AddCircle.coe_nsmul, nsmul_eq_mul,
      mul_one_div]
  · intro H cor hcor y
    have hy : y ∈ Submodule.span ℤ {(groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom uF} := by
      rw [hspan H]; exact Submodule.mem_top
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [addMonoidHom_map_int_smul _ _ cor, hcor, addMonoidHom_map_int_smul _ _ invG, map_nsmul, huG,
      addMonoidHom_map_int_smul _ _ (inv H), huH, index_nsmul_one_div_card]

private theorem fc_of_invsys
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F' : Type) [Field E] [NumberField E] [Field F'] [NumberField F'] [Algebra E F'] [IsGalois E F']
    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 F'), (w.adicCompletion F')ˣ →* (AdeleRing (𝓞 F') F')ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F'), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)
    (lam' : ∀ w : HeightOneSpectrum (𝓞 F'),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))
    (hlam' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      (lam' w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' w x) : IdeleClassGroup (𝓞 F') F'))
    (invG' : ↥(groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2) →+ AddCircle (1 : ℚ))
    (inv' : ∀ H : Subgroup (F' ≃ₐ[E] F'), ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) 2) →+ AddCircle (1 : ℚ))
    (hU : Function.Injective invG' ∧ (∀ H : Subgroup (F' ≃ₐ[E] F'), Function.Injective (inv' H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG'.range ↔ Nat.card (F' ≃ₐ[E] F') • t = 0) ∧
      (∀ (H : Subgroup (F' ≃ₐ[E] F')) (t : AddCircle (1 : ℚ)), t ∈ (inv' H).range ↔ Nat.card ↥H • t = 0) ∧

      (∀ (H : Subgroup (F' ≃ₐ[E] F')) (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2)),
        inv' H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom x) = H.index • invG' x) ∧

      (∀ (w : HeightOneSpectrum (𝓞 F'))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F' w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ]
        (Φ : w.adicCompletion F' ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : w.adicCompletion F'), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F')ˣ) : w.adicCompletion F') = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)),
        m • inv' (NumberField.PlaceDecomp.decomp E F' w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) (lam' w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) θ 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) ∧

      (∀ (H : Subgroup (F' ≃ₐ[E] F'))
        (cor : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) 2) →+ ↥(groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2)),
        (∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2),
          cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom x) = H.index • x) →
        ∀ y : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) 2), invG' (cor y) = inv' H y)) :
    ∃ uF' : groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2,
      invG' uF' = (((1 : ℚ) / (Nat.card (F' ≃ₐ[E] F') : ℚ) : ℚ) : AddCircle (1 : ℚ)) ∧
      (∀ k : ℤ, k • uF' = 0 ↔ (Nat.card (F' ≃ₐ[E] F') : ℤ) ∣ k) ∧
      (∀ (w : HeightOneSpectrum (𝓞 F'))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F' w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ]
        (Φ : w.adicCompletion F' ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : w.adicCompletion F'), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F')ˣ) : w.adicCompletion F') = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)),
        m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) (lam' w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) θ 2).hom u') =
          m • (groupCohomology.map (NumberField.PlaceDecomp.decomp E F' w).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom uF') := by
  classical
  obtain ⟨hinjG, hinj, himG, _him, hres, hiii, _hv⟩ := hU

  have h0 : Nat.card (F' ≃ₐ[E] F') • ((((1 : ℚ) / (Nat.card (F' ≃ₐ[E] F') : ℚ) : ℚ)) : AddCircle (1 : ℚ)) = 0 := by
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div_cancel (by exact_mod_cast (Nat.card_pos (α := F' ≃ₐ[E] F')).ne'),
      AddCircle.coe_eq_zero_iff]
    exact ⟨1, by simp⟩
  obtain ⟨uF', huF'⟩ := (himG _).mpr h0
  refine ⟨uF', huF', ?_, ?_⟩
  ·
    intro k
    have hG0 : (Nat.card (F' ≃ₐ[E] F') : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := F' ≃ₐ[E] F')).ne'
    constructor
    · intro hk
      have h1 : invG' (k • uF') = 0 := by rw [hk, map_zero]
      rw [map_zsmul invG', huF', ← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff] at h1
      obtain ⟨z, hz⟩ := h1
      rw [zsmul_eq_mul, zsmul_eq_mul, mul_one, mul_one_div, eq_div_iff hG0] at hz
      refine ⟨z, ?_⟩
      have hq : (k : ℚ) = ((Nat.card (F' ≃ₐ[E] F') : ℤ) : ℚ) * (z : ℚ) := by push_cast; linarith
      exact_mod_cast hq
    · rintro ⟨z, rfl⟩
      apply hinjG
      rw [map_zsmul invG', huF', map_zero, ← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff]
      refine ⟨z, ?_⟩
      rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]
      push_cast
      field_simp
  ·
    intro w q _ L' _ _ _ Φ h1 h2 h3 K₀ _ hB θ hθ u' hu' m a hm hma
    apply hinj (NumberField.PlaceDecomp.decomp E F' w)
    rw [map_nsmul, hiii w q L' Φ h1 h2 h3 K₀ hB θ hθ u' hu' m a hm hma, map_nsmul, hres, huF', index_nsmul_one_div_card,
      ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div]

private theorem _root_.InvInflAux.basechange
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']

    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))

    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 F'), (w.adicCompletion F')ˣ →* (AdeleRing (𝓞 F') F')ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F'), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)
    (lam' : ∀ w : HeightOneSpectrum (𝓞 F'),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))
    (hlam' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      (lam' w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' w x) : IdeleClassGroup (𝓞 F') F')) :
    ∃ (j : Rep.res (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶ Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')),
      (let J : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F' := M4aHerbrand.Bridge.genuineβ F F'
       (Continuous J ∧
        (∀ a : F, J (algebraMap F (AdeleRing (𝓞 F) F) a) = algebraMap F' (AdeleRing (𝓞 F') F') (algebraMap F F' a)) ∧
        (∀ (g' : F' ≃ₐ[E] F') (x : AdeleRing (𝓞 F) F), J (D.act (AlgEquiv.restrictNormalHom F g') x) = D'.act g' (J x)) ∧

        (∀ (T : Set (HeightOneSpectrum (𝓞 E))) (z : (AdeleRing (𝓞 F) F)ˣ),
          (∀ w : HeightOneSpectrum (𝓞 F), w.under (𝓞 E) ∉ T → finPart w z = 1) →
          ∀ w' : HeightOneSpectrum (𝓞 F'), w'.under (𝓞 E) ∉ T →
            finPart w' (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) = 1) ∧

        (∀ (T : Set (HeightOneSpectrum (𝓞 E))) (z : (AdeleRing (𝓞 F) F)ˣ),
          z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F {w | w.under (𝓞 E) ∈ T} →
          Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z ∈
            NumberField.AdeleRing.unitIdelesOutside (𝓞 F') F' {w' | w'.under (𝓞 E) ∈ T}) ∧

        (∀ z : (AdeleRing (𝓞 F) F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) = 1) ∧

        (∀ (z z' : (AdeleRing (𝓞 F) F)ˣ) (w' : HeightOneSpectrum (𝓞 F')),
          finPart (w'.under (𝓞 F)) z = finPart (w'.under (𝓞 F)) z' →
          finPart w' (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) =
            finPart w' (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z'))) ∧
      ((∀ x : (AdeleRing (𝓞 F) F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) =
          Additive.ofMul (QuotientGroup.mk (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') x) : IdeleClassGroup (𝓞 F') F')) ∧
        Function.Injective j.hom ∧
        (∀ c' : Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'), (∀ g' : F' ≃ₐ[E] F', g' ∈ (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker →
            (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')).ρ g' c' = c') → c' ∈ Set.range j.hom))) := by
  exact M4aHerbrand.BaseChangeAux.basechange p hp2 E F F' D hact ι hι lam hlam D' hact' ι' hι' lam' hlam'

p2m_export "InvInflAux" "basechange"

private theorem descent
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']

    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))

    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 F'), (w.adicCompletion F')ˣ →* (AdeleRing (𝓞 F') F')ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F'), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)
    (lam' : ∀ w : HeightOneSpectrum (𝓞 F'),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))
    (hlam' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      (lam' w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' w x) : IdeleClassGroup (𝓞 F') F'))
    (j : Rep.res (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶ Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))
    (hj : ∀ x : (AdeleRing (𝓞 F) F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) =
      Additive.ofMul (QuotientGroup.mk (Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') x) : IdeleClassGroup (𝓞 F') F'))
    (hjinj : Function.Injective j.hom)
    (hjim : ∀ c' : Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'), (∀ g' : F' ≃ₐ[E] F', g' ∈ (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker →
      (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')).ρ g' c' = c') → c' ∈ Set.range j.hom)
    (uF' : groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2)
    (hord' : ∀ k : ℤ, k • uF' = 0 ↔ (Nat.card (F' ≃ₐ[E] F') : ℤ) ∣ k)
    (hloc' : ∀ (w : HeightOneSpectrum (𝓞 F'))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F' w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ]
        (Φ : w.adicCompletion F' ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : w.adicCompletion F'), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F')ˣ) : w.adicCompletion F') = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)),
        m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) (lam' w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) θ 2).hom u') =
          m • (groupCohomology.map (NumberField.PlaceDecomp.decomp E F' w).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom uF') :
    ∃ uF : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2,
      (∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S) ∧
      (∀ S : Subgroup (F ≃ₐ[E] F), Submodule.span ℤ
        {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom uF} = ⊤) ∧
      (∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)),
        m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u') =
          m • (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom uF) ∧
      (groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom uF = Module.finrank F F' • uF' := by
  exact M4aHerbrand.exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two p hp2 E F F' D hact ι hι lam hlam D' hact' ι' hι' lam' hlam'
    j hj hjinj hjim uF' hord' hloc'

private theorem finrank_nsmul_one_div_card (E F F' : Type) [Field E] [Field F] [Field F'] [Algebra E F] [Algebra E F'] [Algebra F F']
    [IsScalarTower E F F'] [FiniteDimensional E F'] [IsGalois E F] [IsGalois E F'] :
    Module.finrank F F' • ((((1 : ℚ) / (Nat.card (F' ≃ₐ[E] F') : ℚ) : ℚ)) : AddCircle (1 : ℚ)) =
      (((1 : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  haveI : FiniteDimensional E F := FiniteDimensional.left E F F'
  haveI : FiniteDimensional F F' := FiniteDimensional.right E F F'
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, ← Module.finrank_mul_finrank E F F']
  exact nsmul_one_div_mul Module.finrank_pos.ne' Module.finrank_pos.ne'

end InvInflAux

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']

    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))

    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 F'), (w.adicCompletion F')ˣ →* (AdeleRing (𝓞 F') F')ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F'), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)
    (lam' : ∀ w : HeightOneSpectrum (𝓞 F'),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))
    (hlam' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      (lam' w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' w x) : IdeleClassGroup (𝓞 F') F'))

    (invG' : ↥(groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2) →+ AddCircle (1 : ℚ))
    (inv' : ∀ H : Subgroup (F' ≃ₐ[E] F'), ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) 2) →+ AddCircle (1 : ℚ))
    (hinv'sys :
      (      Function.Injective invG' ∧ (∀ H : Subgroup (F' ≃ₐ[E] F'), Function.Injective (inv' H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG'.range ↔ Nat.card (F' ≃ₐ[E] F') • t = 0) ∧
      (∀ (H : Subgroup (F' ≃ₐ[E] F')) (t : AddCircle (1 : ℚ)), t ∈ (inv' H).range ↔ Nat.card ↥H • t = 0) ∧

      (∀ (H : Subgroup (F' ≃ₐ[E] F')) (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2)),
        inv' H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom x) = H.index • invG' x) ∧

      (∀ (w : HeightOneSpectrum (𝓞 F'))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F' w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ]
        (Φ : w.adicCompletion F' ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : w.adicCompletion F'), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F')ˣ) : w.adicCompletion F') = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)),
        m • inv' (NumberField.PlaceDecomp.decomp E F' w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) (lam' w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) θ 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) ∧

      (∀ (H : Subgroup (F' ≃ₐ[E] F'))
        (cor : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) 2) →+ ↥(groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2)),
        (∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2),
          cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom x) = H.index • x) →
        ∀ y : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) 2), invG' (cor y) = inv' H y)))
    :
    ∃ (J : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F')
      (j : Rep.res (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶ Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))
      (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ))
      (inv : ∀ H : Subgroup (F ≃ₐ[E] F), ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ AddCircle (1 : ℚ)),

      (Continuous J ∧
        (∀ a : F, J (algebraMap F (AdeleRing (𝓞 F) F) a) = algebraMap F' (AdeleRing (𝓞 F') F') (algebraMap F F' a)) ∧
        (∀ (g' : F' ≃ₐ[E] F') (x : AdeleRing (𝓞 F) F), J (D.act (AlgEquiv.restrictNormalHom F g') x) = D'.act g' (J x)) ∧

        (∀ (T : Set (HeightOneSpectrum (𝓞 E))) (z : (AdeleRing (𝓞 F) F)ˣ),
          (∀ w : HeightOneSpectrum (𝓞 F), w.under (𝓞 E) ∉ T → finPart w z = 1) →
          ∀ w' : HeightOneSpectrum (𝓞 F'), w'.under (𝓞 E) ∉ T →
            finPart w' (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) = 1) ∧

        (∀ (T : Set (HeightOneSpectrum (𝓞 E))) (z : (AdeleRing (𝓞 F) F)ˣ),
          z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F {w | w.under (𝓞 E) ∈ T} →
          Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z ∈
            NumberField.AdeleRing.unitIdelesOutside (𝓞 F') F' {w' | w'.under (𝓞 E) ∈ T}) ∧

        (∀ z : (AdeleRing (𝓞 F) F)ˣ, infPart z = 1 → infPart (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) = 1) ∧

        (∀ (z z' : (AdeleRing (𝓞 F) F)ˣ) (w' : HeightOneSpectrum (𝓞 F')),
          finPart (w'.under (𝓞 F)) z = finPart (w'.under (𝓞 F)) z' →
          finPart w' (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z) =
            finPart w' (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') z'))) ∧

      ((∀ x : (AdeleRing (𝓞 F) F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) =
          Additive.ofMul (QuotientGroup.mk (Units.map (J : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F') F') x) : IdeleClassGroup (𝓞 F') F')) ∧
        Function.Injective j.hom ∧
        (∀ c' : Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'), (∀ g' : F' ≃ₐ[E] F', g' ∈ (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker →
            (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')).ρ g' c' = c') → c' ∈ Set.range j.hom)) ∧

      (
      Function.Injective invG ∧ (∀ H : Subgroup (F ≃ₐ[E] F), Function.Injective (inv H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0) ∧
      (∀ (H : Subgroup (F ≃ₐ[E] F)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F)) (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
        inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) = H.index • invG x) ∧

      (∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)),
        m • inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F))
        (cor : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
        (∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2),
          cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) = H.index • x) →
        ∀ y : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2), invG (cor y) = inv H y) ∧

      (∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2),
        invG' ((groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom x) = invG x)) := by
  classical

  obtain ⟨j, hA, hB⟩ := InvInflAux.basechange p hp2 E F F' D hact ι hι lam hlam D' hact' ι' hι' lam' hlam'

  obtain ⟨uF', huG', hord', hloc'⟩ := InvInflAux.fc_of_invsys p hp2 E F' D' hact' ι' hι' lam' hlam' invG' inv' hinv'sys

  obtain ⟨uF, hcard, hspan, hloc, hinf⟩ :=
    InvInflAux.descent p hp2 E F F' D hact ι hι lam hlam D' hact' ι' hι' lam' hlam' j hB.1 hB.2.1 hB.2.2 uF' hord' hloc'

  obtain ⟨invG, inv, h1, h2, h3, h4, h5, h6, h7, huG⟩ := InvInflAux.invsys_of_fc p hp2 E F D hact ι hι lam hlam uF hcard hspan hloc
  refine ⟨M4aHerbrand.Bridge.genuineβ F F', j, invG, inv, hA, hB, h1, h2, h3, h4, h5, h6, h7, ?_⟩

  intro x
  have hGx : Nat.card (F ≃ₐ[E] F) • invG x = 0 := (h3 (invG x)).mp ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := InvInflAux.exists_eq_zsmul_one_div_of_nsmul_eq_zero (Nat.card_pos (α := F ≃ₐ[E] F)).ne' (invG x) hGx
  have hx : x = z • uF := by
    apply h1
    rw [hz, ← huG, ← map_zsmul invG]
  haveI : FiniteDimensional E F' := inferInstance
  rw [hx, map_zsmul ((groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom), hinf,
    map_zsmul invG', map_nsmul invG', huG', InvInflAux.finrank_nsmul_one_div_card E F F', map_zsmul invG, huG]

end S_M4aHerbrand_exists_adeleBaseChange_invariant_groupCohomology_ideleClassGroup_map_eq_of_invariant
end P2MW
export P2MW.S_M4aHerbrand_exists_adeleBaseChange_invariant_groupCohomology_ideleClassGroup_map_eq_of_invariant (solution)
