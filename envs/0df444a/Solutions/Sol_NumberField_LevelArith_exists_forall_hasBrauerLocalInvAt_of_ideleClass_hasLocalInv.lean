-- Prove2me | solution 1 for NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5a512f0f-25da-5f0b-a9fc-5eeeae6748c3

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantChar
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_SUnitsModule
import Theorems.Thm_NumberField_LevelArith_exists_le_isUnramifiedOutside_isGalois_forall_map_isPrincipal
import Theorems.Thm_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation
import Theorems.Thm_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep
import Theorems.Thm_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv.NumberField.LevelArith"
p2m_open_scoped "Classical NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv.NumberField.LevelArith TensorProduct Pointwise"
p2m_open_scoped "NumberField P2MW.S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv.NumberField NumberField.PlaceDecomp"
open M4aHerbrand
open IsDedekindDomain
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NumberField
p2m_export "NumberField" "RingOfIntegers.mapRingHom mk RingOfIntegers RingOfIntegers.mapRingEquiv AdeleRing RingOfIntegers.ext SUnits.toUnitsRep SUnits.val PlaceDecomp.decomp IdeleLocalInv.HasLocalInv placesOverPrimes LevelArith.exists_le_isUnramifiedOutside_isGalois_forall_map_isPrincipal IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation LevelArith.exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelFieldEquiv coe_levelFieldEquiv placesOverPrimes placesOverPrimesFinset sUnitsMaxRep HasBrauerLocalInvAt exists_le_isUnramifiedOutside_isGalois_forall_map_isPrincipal exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective"
namespace RealFromIdele
p2m_open "NumberField.LevelArith NumberField"

section LevelInstances
variable (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)

noncomputable def levelFieldAlgEquiv : ↥F ≃ₐ[ℚ] ↥(levelField L F hLF) :=
  AlgEquiv.ofRingEquiv (f := levelFieldEquiv L F hLF) (fun r => by
    apply Subtype.ext
    rw [coe_levelFieldEquiv]
    rfl)

theorem normal_levelField [Normal ℚ ↥F] : Normal ℚ ↥(levelField L F hLF) :=
  Normal.of_algEquiv (levelFieldAlgEquiv L F hLF)

theorem isGalois_levelField [Normal ℚ ↥F] : IsGalois ↥L ↥(levelField L F hLF) := by
  haveI := normal_levelField L F hLF
  haveI : IsGalois ℚ ↥(levelField L F hLF) := IsGalois.mk
  exact IsGalois.tower_top_of_isGalois ℚ ↥L ↥(levelField L F hLF)

end LevelInstances

theorem isPrincipal_map_of_capitulation {p : ℕ} (L F F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (hLF'' : L ≤ F'') (hFF'' : F ≤ F'')
    [Algebra ↥(levelField L F hLF) ↥(levelField L F'' hLF'')]
    (halg : ∀ y : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') y : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ))
    (hcapF : ∀ (I : Ideal (𝓞 ↥F)) (k : ℕ) (a : 𝓞 ↥F), a ≠ 0 → I ^ p ^ k = Ideal.span {a} →
      (I.map (RingOfIntegers.mapRingHom (IntermediateField.inclusion hFF'').toRingHom)).IsPrincipal)
    (I : Ideal (𝓞 ↥(levelField L F hLF))) (k : ℕ) (a : 𝓞 ↥(levelField L F hLF)) (ha : a ≠ 0) (hI : I ^ p ^ k = Ideal.span {a}) :
    (I.map (algebraMap (𝓞 ↥(levelField L F hLF)) (𝓞 ↥(levelField L F'' hLF'')))).IsPrincipal := by
  let e₁ : 𝓞 ↥F ≃+* 𝓞 ↥(levelField L F hLF) := RingOfIntegers.mapRingEquiv (levelFieldEquiv L F hLF)
  let e₂ : 𝓞 ↥F'' ≃+* 𝓞 ↥(levelField L F'' hLF'') := RingOfIntegers.mapRingEquiv (levelFieldEquiv L F'' hLF'')

  set I₀ : Ideal (𝓞 ↥F) := I.map (e₁.symm : 𝓞 ↥(levelField L F hLF) →+* 𝓞 ↥F) with hI₀
  have ha₀ : e₁.symm a ≠ 0 := fun h => ha (by simpa using congrArg e₁ h)
  have hI₀' : I₀ ^ p ^ k = Ideal.span {e₁.symm a} := by
    rw [hI₀, ← Ideal.map_pow, hI, Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨b, hb⟩ := (hcapF I₀ k (e₁.symm a) ha₀ hI₀').principal

  have hsq : (algebraMap (𝓞 ↥(levelField L F hLF)) (𝓞 ↥(levelField L F'' hLF''))).comp (e₁ : 𝓞 ↥F →+* 𝓞 ↥(levelField L F hLF)) =
      (e₂ : 𝓞 ↥F'' →+* 𝓞 ↥(levelField L F'' hLF'')).comp (RingOfIntegers.mapRingHom (IntermediateField.inclusion hFF'').toRingHom) := by
    apply RingHom.ext
    intro y
    apply RingOfIntegers.ext
    apply Subtype.ext
    show (((algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') (levelFieldEquiv L F hLF (y : ↥F))) : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ) =
      ((levelFieldEquiv L F'' hLF'' (IntermediateField.inclusion hFF'' (y : ↥F)) : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ)
    rw [halg, coe_levelFieldEquiv, coe_levelFieldEquiv]
    rfl
  have hIe : I = I₀.map (e₁ : 𝓞 ↥F →+* 𝓞 ↥(levelField L F hLF)) := by
    rw [hI₀, Ideal.map_map, show (e₁ : 𝓞 ↥F →+* 𝓞 ↥(levelField L F hLF)).comp (e₁.symm : 𝓞 ↥(levelField L F hLF) →+* 𝓞 ↥F) = RingHom.id _ from
      RingHom.ext (fun z => e₁.apply_symm_apply z), Ideal.map_id]
  rw [hIe, Ideal.map_map, hsq, ← Ideal.map_map, show I₀.map (RingOfIntegers.mapRingHom (IntermediateField.inclusion hFF'').toRingHom) =
      Ideal.span {b} from hb, Ideal.map_span, Set.image_singleton]
  exact ⟨⟨e₂ b, rfl⟩⟩

end NumberField.LevelArith.RealFromIdele

open _root_.NumberField (AdeleRing) in
open NumberField.LevelArith.RealFromIdele in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)
    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (hactI : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • y = D.unitsAct g y)
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))]
    (hact : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (c : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))), g • c = D.classAct g c)
    (prG : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
      Rep.res (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w)) (w.adicCompletion ↥(levelField L F hLF))ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))
    (π : Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ ⟶ Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))
    (hπ : ∀ y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ, π.hom (Additive.ofMul y) = Additive.ofMul (QuotientGroup.mk y : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))))
    (x : groupCohomology (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) 2) (k : ℕ) (hxk : (p ^ k : ℤ) • x = 0)
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)), (∀ v ∈ placesOverPrimesFinset ↥L S, w.asIdeal.comap (algebraMap (𝓞 ↥L) (𝓞 ↥(levelField L F hLF))) ≠ v.asIdeal) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom x = 0)
    (hπx : (groupCohomology.map (MonoidHom.id (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) π 2).hom x = 0)
    (t : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ))
    (ht : ∀ v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)), NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI x v.1 (t v)) :
    ∃ a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))), ∀ v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)), HasBrauerLocalInvAt p S L a v (t v) := by

  obtain ⟨F'', hFF'', fdF'', hF'', hGal'', hcapF⟩ :=
    NumberField.LevelArith.exists_le_isUnramifiedOutside_isGalois_forall_map_isPrincipal (p := p) S hpS F hF
  haveI := fdF''
  haveI : IsGalois ℚ ↥F'' := hGal''
  haveI : Normal ℚ ↥F'' := inferInstance
  have hLF'' : L ≤ F'' := hLF.trans hFF''
  haveI : IsGalois ↥L ↥(levelField L F'' hLF'') := isGalois_levelField L F'' hLF''

  have hK : levelField L F hLF ≤ levelField L F'' hLF'' := fun x hx => hFF'' hx
  letI algK : Algebra ↥(levelField L F hLF) ↥(levelField L F'' hLF'') := (IntermediateField.inclusion hK).toRingHom.toAlgebra
  haveI : IsScalarTower ↥L ↥(levelField L F hLF) ↥(levelField L F'' hLF'') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halg : ∀ y : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') y : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ) := fun _ => rfl

  let D'' : IdeleGaloisDescent (𝓞 ↥(levelField L F'' hLF'')) ↥L ↥(levelField L F'' hLF'') := M4aHerbrand.GenuineDescent.genuineDescentDatum ↥L ↥(levelField L F'' hLF'')
  letI instI'' : MulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ := MulDistribMulAction.compHom _ D''.unitsAct
  have hactI'' : ∀ (g : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF''))) (y : (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ), g • y = D''.unitsAct g y := fun _ _ => rfl
  let jK : Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (↥(levelField L F'' hLF''))ˣ ⟶ Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ :=
    M4aHerbrand.repHomOfMulEquivariant (Units.map (algebraMap ↥(levelField L F'' hLF'') (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')) : ↥(levelField L F'' hLF'') →* (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')))) (fun g u => by
      apply Units.ext
      show algebraMap ↥(levelField L F'' hLF'') (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')) (g • (u : ↥(levelField L F'' hLF''))) = D''.act g (algebraMap ↥(levelField L F'' hLF'') (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')) (u : ↥(levelField L F'' hLF'')))
      rw [D''.compat]
      rfl)
  let j'' := NumberField.SUnits.toUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) ≫ jK
  have hj'' : ∀ y, Additive.toMul (j''.hom y) =
      Units.map (algebraMap ↥(levelField L F'' hLF'') (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')) : ↥(levelField L F'' hLF'') →* (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))) (NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) y) :=
    fun y => rfl
  obtain ⟨ι'', hι'', φ'', hbij'', hval''⟩ :=
    NumberField.LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective S L F'' hLF'' hF''

  have hcap : ∀ (I : Ideal (𝓞 ↥(levelField L F hLF))) (k : ℕ) (a : 𝓞 ↥(levelField L F hLF)), a ≠ 0 → I ^ p ^ k = Ideal.span {a} →
      (I.map (algebraMap (𝓞 ↥(levelField L F hLF)) (𝓞 ↥(levelField L F'' hLF'')))).IsPrincipal :=
    fun I k a ha hI => isPrincipal_map_of_capitulation (p := p) L F F'' hLF hLF'' hFF'' halg hcapF I k a ha hI
  obtain ⟨f, k', hk', htr⟩ :=
    NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_hasLocalInv_of_map_pi_eq_zero_of_capitulation ↥L ↥(levelField L F hLF) ↥(levelField L F'' hLF'')
      (placesOverPrimesFinset ↥L S) D hactI hact prG hprG π hπ D'' hactI'' j'' hj'' p hcap x k hxk hsupp hπx

  exact NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep S hpS L hL h4 F'' hLF'' hF''
    ι'' hι'' φ'' hbij'' hval'' D'' hactI'' j'' hj'' f k' hk' t (fun v => htr v.1 (t v) (ht v))

end S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv
end P2MW
export P2MW.S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_ideleClass_hasLocalInv (solution)
