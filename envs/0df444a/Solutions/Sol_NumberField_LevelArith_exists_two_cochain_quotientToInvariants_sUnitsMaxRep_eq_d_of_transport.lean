-- Prove2me | solution 1 for NumberField.LevelArith.exists_two_cochain_quotientToInvariants_sUnitsMaxRep_eq_d_of_transport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ac789289-4012-565d-a631-e2c039f3868d

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_two_cochain_quotientToInvariants_sUnitsMaxRep_eq_d_of_transport

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

set_option maxHeartbeats 4000000 in
theorem solution
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF₂ : L ≤ F₂) [FiniteDimensional ℚ ↥F₂] [Normal ℚ ↥F₂] [IsGalois ↥L ↥(levelField L F₂ hLF₂)]
    (ι₂ : (↥(levelField L F₂ hLF₂) ≃ₐ[↥L] ↥(levelField L F₂ hLF₂)) →* (↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι₂ : ∀ g : ↥L.fixingSubgroup, ι₂ (levelGal L F₂ hLF₂ g) = (g : (↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (φ₂ : Rep.res ι₂ ((sUnitsMaxRep S L).quotientToInvariants (F₂.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ hLF₂) (placesOverPrimesFinset ↥L S)))
    (hφ₂ : Function.Bijective φ₂.hom)
    (hφval₂ : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F₂ hLF₂) (placesOverPrimesFinset ↥L S) (φ₂.hom x) : ↥(levelField L F₂ hLF₂)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : ((Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))))
    (e₂ : (Fin 2 → (↥(levelField L F₂ hLF₂) ≃ₐ[↥L] ↥(levelField L F₂ hLF₂))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ hLF₂) (placesOverPrimesFinset ↥L S)))
    (hfe₂ : ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((NumberField.SUnits.val ↥L ↥(levelField L F₂ hLF₂) (placesOverPrimesFinset ↥L S) (((inhomogeneousCochains (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ hLF₂) (placesOverPrimesFinset ↥L S))).d 2 3).hom e₂ (fun i => levelGal L F₂ hLF₂ (g i))) : ↥(levelField L F₂ hLF₂)) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) :
    ∃ b : ((Fin 2 → (↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b (fun i => (g i : (↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by
  classical
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : Normal ↥L (AlgebraicClosure ℚ) := Normal.tower_top_of_normal ℚ ↥L (AlgebraicClosure ℚ)

  have hsurjLG : Function.Surjective (levelGal L F₂ hLF₂) :=
    (AlgEquiv.restrictNormalHom_surjective _).comp (IntermediateField.fixingSubgroupEquiv L).surjective
  have hι₂inj : Function.Injective ι₂ := by
    intro a b hab
    obtain ⟨γa, rfl⟩ := hsurjLG a
    obtain ⟨γb, rfl⟩ := hsurjLG b
    rw [hι₂, hι₂, QuotientGroup.eq] at hab
    have h1 : levelGal L F₂ hLF₂ (γa⁻¹ * γb) = 1 :=
      levelGal_eq_one_of_mem L F₂ hLF₂ _ (Subgroup.mem_comap.mp hab)
    rwa [map_mul, map_inv, inv_mul_eq_one] at h1
  have hι₂surj : Function.Surjective ι₂ := by
    intro x
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨levelGal L F₂ hLF₂ γ, hι₂ γ⟩
  let κ := (MulEquiv.ofBijective ι₂ ⟨hι₂inj, hι₂surj⟩).symm
  have hκι : ∀ γ, κ (ι₂ γ) = γ := fun γ => (MulEquiv.ofBijective ι₂ ⟨hι₂inj, hι₂surj⟩).symm_apply_apply γ

  let ψ := (Equiv.ofBijective φ₂.hom hφ₂).symm
  have hψ : ∀ y, φ₂.hom (ψ y) = y := (Equiv.ofBijective φ₂.hom hφ₂).apply_symm_apply

  let T := groupCohomology.cochainsMap ι₂ φ₂
  have hcomm : ∀ (i j : ℕ) x,
      ((inhomogeneousCochains (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ hLF₂)
        (placesOverPrimesFinset ↥L S))).d i j).hom ((T.f i).hom x) =
      (T.f j).hom (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants
        (F₂.fixingSubgroup.comap L.fixingSubgroup.subtype))).d i j).hom x) := fun i j x =>
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (T.comm i j)) x
  have hT : ∀ (n : ℕ) (c : (Fin n → (↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype)) →
      ((sUnitsMaxRep S L).quotientToInvariants (F₂.fixingSubgroup.comap L.fixingSubgroup.subtype)))
      (γ : Fin n → (↥(levelField L F₂ hLF₂) ≃ₐ[↥L] ↥(levelField L F₂ hLF₂))),
      (T.f n).hom c γ = φ₂.hom (c (fun i => ι₂ (γ i))) := fun n c γ => rfl

  refine ⟨fun x => ψ (e₂ (fun i => κ (x i))), fun g => ?_⟩
  have hTb : (T.f 2).hom (fun x => ψ (e₂ (fun i => κ (x i)))) = e₂ := by
    funext γ
    rw [hT, hψ]
    congr 1
    funext i
    exact hκι (γ i)
  have hd := hcomm 2 3 (fun x => ψ (e₂ (fun i => κ (x i))))
  rw [hTb] at hd
  have key := congrFun hd (fun i => levelGal L F₂ hLF₂ (g i))
  rw [hT] at key
  have hg : (fun i => ι₂ (levelGal L F₂ hLF₂ (g i))) =
      fun i => (g i : ↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
    funext fun i => hι₂ (g i)
  rw [hg] at key
  have h1 := congrArg (fun y => ((NumberField.SUnits.val ↥L ↥(levelField L F₂ hLF₂)
    (placesOverPrimesFinset ↥L S) y : ↥(levelField L F₂ hLF₂)) : AlgebraicClosure ℚ)) key
  simp only at h1
  rw [hφval₂, hfe₂ g] at h1

  exact Subtype.ext (Additive.toMul.injective (Units.val_injective h1))

end S_NumberField_LevelArith_exists_two_cochain_quotientToInvariants_sUnitsMaxRep_eq_d_of_transport
end P2MW
export P2MW.S_NumberField_LevelArith_exists_two_cochain_quotientToInvariants_sUnitsMaxRep_eq_d_of_transport (solution)
