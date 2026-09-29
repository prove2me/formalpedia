-- Prove2me | solution 1 for NumberField.LevelArith.map_prG_map_principalIdele_eq_zero_of_forall_comap_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5a39d09b-5aeb-543f-a16f-27394604bcdd

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
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one
import Theorems.Thm_NumberField_LevelArith_ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_map_prG_map_principalIdele_eq_zero_of_forall_comap_ne

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise
p2m_open_scoped "NumberField P2MW.S_NumberField_LevelArith_map_prG_map_principalIdele_eq_zero_of_forall_comap_ne.NumberField NumberField.PlaceDecomp"
open M4aHerbrand
open IsDedekindDomain

section BetaGeneric
p2m_open "NumberField P2MW.S_NumberField_LevelArith_map_prG_map_principalIdele_eq_zero_of_forall_comap_ne.NumberField"

namespace OffS

variable (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
variable (T : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 K))

noncomputable abbrev locw : K →+* w.adicCompletion K := algebraMap K _

theorem smul_locw (σ : NumberField.PlaceDecomp.decomp E K w) (x : K) :
    σ • locw K w x = locw K w ((σ : K ≃ₐ[E] K) x) := by
  rw [NumberField.PlaceDecomp.smul_def, show locw K w = algebraMap K _ from rfl,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, WithVal.equiv_symm_apply]
  rw [NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
  rfl

theorem valued_locw (x : K) : Valued.v (locw K w x) = w.valuation K x := by
  rw [show locw K w = algebraMap K _ from rfl, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem finPart_map_algebraMap (x : Kˣ) :
    finPart w (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) x) =
      Units.map (locw K w : K →* w.adicCompletion K) x := by
  apply Units.ext
  rw [coe_finPart_apply, Units.coe_map, Units.coe_map, MonoidHom.coe_coe, NumberField.AdeleRing.algebraMap_snd_apply,
    MonoidHom.coe_coe, show locw K w = algebraMap K _ from rfl, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  rfl

variable {T w}

theorem valuation_val_eq_one (hw : w.under (𝓞 E) ∉ T) (u : NumberField.SUnits.sUnitsRep E K T) :
    w.valuation K (NumberField.SUnits.val E K T u : K) = 1 := by
  have h := (NumberField.SUnits.mem_sUnits_iff E K T (NumberField.SUnits.val E K T u)).1
    (NumberField.SUnits.val_mem E K T u) 1 w hw
  rwa [AlgEquiv.one_apply] at h

theorem map_val_mem_unitGroup (hw : w.under (𝓞 E) ∉ T) (u : NumberField.SUnits.sUnitsRep E K T) :
    Units.map (locw K w : K →* w.adicCompletion K) (NumberField.SUnits.val E K T u) ∈ (w.adicCompletionIntegers K).unitGroup := by
  show _ ∈ (Valued.v (R := w.adicCompletion K)).valuationSubring.unitGroup
  rw [Valuation.mem_unitGroup_iff, Units.coe_map, MonoidHom.coe_coe, valued_locw, valuation_val_eq_one E K hw u]

noncomputable def toIntegerUnit (hw : w.under (𝓞 E) ∉ T) (u : NumberField.SUnits.sUnitsRep E K T) : (w.adicCompletionIntegers K)ˣ :=
  (w.adicCompletionIntegers K).unitGroupMulEquiv ⟨_, map_val_mem_unitGroup E K hw u⟩

theorem coe_coe_toIntegerUnit (hw : w.under (𝓞 E) ∉ T) (u : NumberField.SUnits.sUnitsRep E K T) :
    ((toIntegerUnit E K hw u : w.adicCompletionIntegers K) : w.adicCompletion K) = locw K w (NumberField.SUnits.val E K T u : K) :=
  ValuationSubring.coe_unitGroupMulEquiv_apply _ _

theorem map_subtype_toIntegerUnit (hw : w.under (𝓞 E) ∉ T) (u : NumberField.SUnits.sUnitsRep E K T) :
    Units.map (w.adicCompletionIntegers K).subtype.toMonoidHom (toIntegerUnit E K hw u) =
      Units.map (locw K w : K →* w.adicCompletion K) (NumberField.SUnits.val E K T u) :=
  Units.ext (coe_coe_toIntegerUnit E K hw u)

theorem toIntegerUnit_add (hw : w.under (𝓞 E) ∉ T) (u u' : NumberField.SUnits.sUnitsRep E K T) :
    toIntegerUnit E K hw (u + u') = toIntegerUnit E K hw u * toIntegerUnit E K hw u' := by
  apply Units.ext; apply Subtype.ext
  rw [coe_coe_toIntegerUnit, Units.val_mul, MulMemClass.coe_mul, coe_coe_toIntegerUnit, coe_coe_toIntegerUnit,
    NumberField.SUnits.val_add, Units.val_mul, map_mul]

end OffS

namespace OffS

variable (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
variable {T : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 K)}

noncomputable abbrev OU (w : HeightOneSpectrum (𝓞 K)) : Rep ℤ ↥(NumberField.PlaceDecomp.decomp E K w) :=
  Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ

noncomputable def incl (w : HeightOneSpectrum (𝓞 K)) :
    OU E K w ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ :=
  M4aHerbrand.repHomOfMulEquivariant (Units.map (w.adicCompletionIntegers K).subtype.toMonoidHom) (fun _ _ => Units.ext rfl)

theorem toIntegerUnit_ρ (hw : w.under (𝓞 E) ∉ T) (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (u : NumberField.SUnits.sUnitsRep E K T) :
    toIntegerUnit E K hw ((NumberField.SUnits.sUnitsRep E K T).ρ (g : K ≃ₐ[E] K) u) = g • toIntegerUnit E K hw u := by
  apply Units.ext; apply Subtype.ext
  have h1 : NumberField.SUnits.val E K T ((NumberField.SUnits.sUnitsRep E K T).ρ (g : K ≃ₐ[E] K) u) =
      (g : K ≃ₐ[E] K) • NumberField.SUnits.val E K T u := rfl
  have h2 : ∀ x : Kˣ, (((g : K ≃ₐ[E] K) • x : Kˣ) : K) = (g : K ≃ₐ[E] K) (x : K) := fun _ => rfl
  have h3 : ∀ U : (w.adicCompletionIntegers K)ˣ,
      (((g • U : (w.adicCompletionIntegers K)ˣ) : w.adicCompletionIntegers K) : w.adicCompletion K) =
        g • ((U : w.adicCompletionIntegers K) : w.adicCompletion K) := fun _ => rfl
  rw [coe_coe_toIntegerUnit, h1, h2, h3, coe_coe_toIntegerUnit, smul_locw]

noncomputable def c0 (hw : w.under (𝓞 E) ∉ T) :
    Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (NumberField.SUnits.sUnitsRep E K T) ⟶ OU E K w :=
  Rep.ofHom ⟨(AddMonoidHom.mk' (fun u : NumberField.SUnits.sUnitsRep E K T => Additive.ofMul (toIntegerUnit E K hw u))
      (fun u u' => by
        show Additive.ofMul (toIntegerUnit E K hw (u + u')) =
          Additive.ofMul (toIntegerUnit E K hw u) + Additive.ofMul (toIntegerUnit E K hw u')
        rw [toIntegerUnit_add]; rfl)).toIntLinearMap, fun g => by
    refine LinearMap.ext fun u => ?_
    change Additive.ofMul (toIntegerUnit E K hw ((NumberField.SUnits.sUnitsRep E K T).ρ (g : K ≃ₐ[E] K) u)) =
      Additive.ofMul (g • toIntegerUnit E K hw u)
    rw [toIntegerUnit_ρ]⟩

theorem c0_hom_apply (hw : w.under (𝓞 E) ∉ T) (u : NumberField.SUnits.sUnitsRep E K T) :
    (c0 E K hw).hom u = Additive.ofMul (toIntegerUnit E K hw u) := rfl

theorem res_j_comp_prG_eq (hw : w.under (𝓞 E) ∉ T)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (x : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (j : NumberField.SUnits.sUnitsRep E K T ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hj : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K T y)) :
    (Rep.resFunctor (NumberField.PlaceDecomp.decomp E K w).subtype).map j ≫ prG w = c0 E K hw ≫ incl E K w := by
  ext u
  change (prG w).hom (j.hom u) = (incl E K w).hom ((c0 E K hw).hom u)
  have hl : (prG w).hom (j.hom u) = Additive.ofMul (finPart w (Additive.toMul (j.hom u))) := by
    rw [← hprG]; rfl
  rw [hl]
  erw [hj]
  rw [finPart_map_algebraMap, ← map_subtype_toIntegerUnit E K hw u]
  rfl

end OffS

namespace OffS

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

section maps
universe u
variable {k : Type u} [CommRing k] {G : Type u} [Group G]

theorem map_subtype_map_id_apply (S : Subgroup G) {A B : Rep k G} {C : Rep k S}
    (φ : A ⟶ B) (ψ : Rep.res S.subtype B ⟶ C) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map S.subtype ψ n).hom ((groupCohomology.map (MonoidHom.id G) φ n).hom x) =
      (groupCohomology.map S.subtype ((Rep.resFunctor S.subtype).map φ ≫ ψ) n).hom x := by
  have h := groupCohomology.map_comp (MonoidHom.id G) S.subtype φ ψ n
  have h' : groupCohomology.map S.subtype ((Rep.resFunctor S.subtype).map φ ≫ ψ) n =
      groupCohomology.map (MonoidHom.id G) φ n ≫ groupCohomology.map S.subtype ψ n := h
  rw [h']
  rfl

theorem map_comp_id_apply {H : Type u} [Group H] {A : Rep k H} {B C : Rep k G} (f : G →* H)
    (φ : Rep.res f A ⟶ B) (ψ : B ⟶ C) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map f (φ ≫ ψ) n).hom x =
      (groupCohomology.map (MonoidHom.id G) ψ n).hom ((groupCohomology.map f φ n).hom x) := by
  rw [show groupCohomology.map f (φ ≫ ψ) n = groupCohomology.map f φ n ≫ groupCohomology.map (MonoidHom.id G) ψ n from
    groupCohomology.map_comp f (MonoidHom.id G) φ ψ n]
  rfl

end maps

theorem subsingleton_H2_OU [IsGalois E K] {w : HeightOneSpectrum (𝓞 K)}
    (hw : (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1) :
    Subsingleton (groupCohomology (OU E K w) 2) := by
  classical
  letI : Fintype ↥(NumberField.PlaceDecomp.decomp E K w) := Fintype.ofFinite _
  exact NumberField.PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one E K w hw 2

end OffS

namespace NumberField p2m_export "NumberField" "AdeleRing.algebraMap_snd_apply place AdeleRing SUnits.under_above SUnits.mem_sUnits_iff SUnits.sUnitsRep SUnits.val SUnits.val_add SUnits.val_mem PlaceAbove.above PlaceDecomp.decomp PlaceDecomp.actRingEquiv_coe PlaceDecomp.smul_def PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one LevelArith.ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset" namespace SUnits p2m_export "NumberField.SUnits" "under_above mem_sUnits_iff sUnitsRep val val_add val_mem" end NumberField.SUnits
p2m_open_scoped "NumberField NumberField.SUnits" in

theorem NumberField.SUnits.map_prG_map_sUnitsRep_eq_zero_of_under_not_mem_of_ramificationIdx_eq_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ T → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (x : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (j : NumberField.SUnits.sUnitsRep E K T ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hj : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K T y))
    (y : groupCohomology (NumberField.SUnits.sUnitsRep E K T) 2)
    (w : HeightOneSpectrum (𝓞 K)) (hw : w.under (𝓞 E) ∉ T) :
    (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom
      ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) j 2).hom y) = 0 := by
  classical
  haveI := OffS.subsingleton_H2_OU E K (hunr w hw)

  rw [OffS.map_subtype_map_id_apply, OffS.res_j_comp_prG_eq E K hw prG hprG j hj, OffS.map_comp_id_apply,
    Subsingleton.elim ((groupCohomology.map _ (OffS.c0 E K hw) 2).hom y) 0, map_zero]

p2m_open_scoped "NumberField NumberField.SUnits" in

theorem NumberField.SUnits.map_prG_above_map_sUnitsRep_eq_zero_of_not_mem_of_ramificationIdx_eq_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ T → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1)

    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (x : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (j : NumberField.SUnits.sUnitsRep E K T ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hj : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K T y))
    (y : groupCohomology (NumberField.SUnits.sUnitsRep E K T) 2)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ T) :
    (groupCohomology.map (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)).subtype
        (prG (NumberField.PlaceAbove.above E K v)) 2).hom
      ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) j 2).hom y) = 0 := by
  exact NumberField.SUnits.map_prG_map_sUnitsRep_eq_zero_of_under_not_mem_of_ramificationIdx_eq_one E K T hunr prG hprG j hj y
    (NumberField.PlaceAbove.above E K v) (by rwa [NumberField.SUnits.under_above])

end BetaGeneric

open _root_.NumberField (AdeleRing) in

theorem solution
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]

    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)

    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφ : Function.Bijective φ.hom)
    (hφval : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))

    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (hactI : ∀ (g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • x = D.unitsAct g x)

    (j : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (hj : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))
        (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y))

    (prG : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
      Rep.res (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w)) (w.adicCompletion ↥(levelField L F hLF))ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))

    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)))
    (hw : ∀ v ∈ placesOverPrimesFinset ↥L S, w.asIdeal.comap (algebraMap (𝓞 ↥L) (𝓞 ↥(levelField L F hLF))) ≠ v.asIdeal) :
    (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom
      ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) = 0 := by
  have _ := hι; have _ := hφ; have _ := hφval; have _ := hactI

  have hwS : w.under (𝓞 ↥L) ∉ placesOverPrimesFinset ↥L S := fun hmem =>
    hw _ hmem (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_def])

  show (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom
      ((groupCohomology.map ι (φ ≫ j) 2).hom (H2π _ f)) = 0
  rw [OffS.map_comp_id_apply]
  exact NumberField.SUnits.map_prG_map_sUnitsRep_eq_zero_of_under_not_mem_of_ramificationIdx_eq_one ↥L ↥(levelField L F hLF)
    (placesOverPrimesFinset ↥L S)
    (fun w' hw' => NumberField.LevelArith.ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset
      S L F hLF hF w' hw')
    prG hprG j hj _ w hwS

end S_NumberField_LevelArith_map_prG_map_principalIdele_eq_zero_of_forall_comap_ne
end P2MW
export P2MW.S_NumberField_LevelArith_map_prG_map_principalIdele_eq_zero_of_forall_comap_ne (solution)
