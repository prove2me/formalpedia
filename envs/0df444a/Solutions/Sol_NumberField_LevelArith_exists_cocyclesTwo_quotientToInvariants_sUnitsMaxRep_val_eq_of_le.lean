-- Prove2me | solution 1 for NumberField.LevelArith.exists_cocyclesTwo_quotientToInvariants_sUnitsMaxRep_val_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/252f5801-9ce7-5bd4-be08-9709dc473945

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
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_cocyclesTwo_quotientToInvariants_sUnitsMaxRep_val_eq_of_le

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem solution
    (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F)
    [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
    ∃ f' : cocycles₂ ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)),
      ∀ (g h : ↥L'.fixingSubgroup) (g₀ h₀ : ↥L.fixingSubgroup),
      ((g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((h₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((sUnitsMaxRep.val S L' ((f' ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L ((f ((g₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
  classical
  have hΓ : L'.fixingSubgroup ≤ L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hLL'
  let incl : ↥L'.fixingSubgroup →* ↥L.fixingSubgroup := Subgroup.inclusion hΓ
  have hU : F.fixingSubgroup.comap L'.fixingSubgroup.subtype ≤
      (F.fixingSubgroup.comap L.fixingSubgroup.subtype).comap incl := fun γ h => h
  let r : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype) →*
      (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
    QuotientGroup.map _ _ incl hU

  have hcar : sUnitsMaxSubmodule S L = sUnitsMaxSubmodule S L' := by
    ext x
    rw [mem_sUnitsMaxSubmodule, mem_sUnitsMaxSubmodule, sUnitsMaxStable_eq_sUnitsMax, sUnitsMaxStable_eq_sUnitsMax]
  have hvalinj : ∀ {x y : sUnitsMaxRep S L'}, sUnitsMaxRep.val S L' x = sUnitsMaxRep.val S L' y → x = y :=
    fun h => Subtype.ext (Additive.toMul.injective h)

  let τ : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) →ₗ[ℤ]
      ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) :=
    { toFun := fun v => ⟨⟨(v.1).1, hcar ▸ (v.1).2⟩, fun γ => by
        have h0 := congrArg (sUnitsMaxRep.val S L) (v.2 ⟨incl γ.1, hU γ.2⟩)
        rw [MonoidHom.comp_apply, sUnitsMaxRep.val_ρ] at h0
        apply hvalinj
        rw [MonoidHom.comp_apply, sUnitsMaxRep.val_ρ]
        exact h0⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hτ : ∀ v, sUnitsMaxRep.val S L' (τ v : sUnitsMaxRep S L') = sUnitsMaxRep.val S L (v : sUnitsMaxRep S L) :=
    fun _ => rfl
  let ψ : Rep.res r ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      (sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype) :=
    Rep.ofHom ⟨τ, fun q => QuotientGroup.induction_on q fun γ => LinearMap.ext fun v => rfl⟩
  refine ⟨(groupCohomology.mapCocycles₂ r ψ).hom f, fun g h g₀ h₀ hg hh => ?_⟩
  have hq : ∀ (γ : ↥L'.fixingSubgroup) (γ₀ : ↥L.fixingSubgroup),
      ((γ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      r (γ : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype) =
        (γ₀ : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) := fun γ γ₀ hγ => by
    change (QuotientGroup.mk (incl γ) : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) = _
    congr 1
    exact Subtype.ext hγ.symm
  show ((sUnitsMaxRep.val S L' ((τ (f (r (g : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype),
      r (h : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) :
      (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
  rw [hq g g₀ hg, hq h h₀ hh]
  exact congrArg Units.val (hτ _)

end S_NumberField_LevelArith_exists_cocyclesTwo_quotientToInvariants_sUnitsMaxRep_val_eq_of_le
end P2MW
export P2MW.S_NumberField_LevelArith_exists_cocyclesTwo_quotientToInvariants_sUnitsMaxRep_val_eq_of_le (solution)
