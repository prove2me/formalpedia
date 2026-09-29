-- Prove2me | solution 1 for NumberField.LevelArith.exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0186dc40-7958-5d9b-bdb6-73dc4ec8a5b7

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
import Theorems.Thm_NumberField_LevelArith_levelGal_surjective_and_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep.NumberField.LevelArith"
p2m_open_scoped "Classical NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep.NumberField.LevelArith TensorProduct Pointwise"
p2m_open_scoped "NumberField P2MW.S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep.NumberField NumberField.PlaceDecomp"
open M4aHerbrand

open _root_.NumberField (AdeleRing)

namespace NumberField
p2m_export "NumberField" "place AdeleRing SUnits.sUnitsRep SUnits.val IdeleLocalInv.HasLocalInv placesOverPrimes LevelArith.levelGal_surjective_and_ker"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal placesOverPrimes placesOverPrimesFinset sUnitsMaxRep sUnitsMaxRep.val HasBrauerLocalInvAt levelGal_surjective_and_ker"
namespace R4
p2m_open "NumberField.LevelArith NumberField"
section MapLemmas
universe uu
variable {k : Type uu} [CommRing k]

theorem map_map_apply {G₁ G₂ G₃ : Type uu} [Group G₁] [Group G₂] [Group G₃]
    {A : Rep k G₃} {B : Rep k G₂} {C : Rep k G₁} (f : G₂ →* G₃) (g : G₁ →* G₂)
    (φ : Rep.res f A ⟶ B) (ψ : Rep.res g B ⟶ C) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map g ψ n).hom ((groupCohomology.map f φ n).hom x) =
      (groupCohomology.map (f.comp g) ((Rep.resFunctor g).map φ ≫ ψ) n).hom x := by
  rw [groupCohomology.map_comp]
  rfl

theorem map_congr_apply {G₁ G₃ : Type uu} [Group G₁] [Group G₃] {A : Rep k G₃} {C : Rep k G₁}
    (f₁ f₂ : G₁ →* G₃) (hf : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ C) (φ₂ : Rep.res f₂ A ⟶ C)
    (h : ∀ x : A, φ₁.hom x = φ₂.hom x) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map f₁ φ₁ n).hom x = (groupCohomology.map f₂ φ₂ n).hom x := by
  subst hf
  have : φ₁ = φ₂ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext h))
  subst this
  rfl

end MapLemmas
end NumberField.LevelArith.R4

open NumberField.LevelArith.R4 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF'' : L ≤ F'') [FiniteDimensional ℚ ↥F''] [Normal ℚ ↥F''] [IsGalois ↥L ↥(levelField L F'' hLF'')]
    (hF'' : F''.IsUnramifiedOutside S)
    (ι'' : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) →* (↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι'' : ∀ g : ↥L.fixingSubgroup, ι'' (levelGal L F'' hLF'' g) = (g : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ'' : Rep.res ι'' ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S))
    (hφ'' : Function.Bijective φ''.hom)
    (hφ''val : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) (φ''.hom x) : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (D'' : IdeleGaloisDescent (𝓞 ↥(levelField L F'' hLF'')) ↥L ↥(levelField L F'' hLF''))
    [MulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ]
    (hactI'' : ∀ (g : ↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (y : (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ), g • y = D''.unitsAct g y)
    (j'' : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ)
    (hj'' : ∀ y, Additive.toMul (j''.hom y) =
      Units.map (algebraMap ↥(levelField L F'' hLF'') (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')) : ↥(levelField L F'' hLF'') →* AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))
        (NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) y))
    (g : cocycles₂ (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S)))
    (k : ℕ) (hk : (p ^ k : ℤ) • (H2π _ g) = 0)
    (t : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ))
    (ht : ∀ v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)),
      NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F'' hLF'') D'' hactI'' ((groupCohomology.map (MonoidHom.id _) j'' 2) (H2π _ g)) v.1 (t v)) :
    ∃ a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))), ∀ v, HasBrauerLocalInvAt p S L a v (t v) := by

  obtain ⟨hlg_surj, hlg_ker⟩ := NumberField.LevelArith.levelGal_surjective_and_ker L F'' hLF''
  have hι_bij : Function.Bijective ι'' := by
    constructor
    · refine (injective_iff_map_eq_one ι'').2 fun σ hσ => ?_
      obtain ⟨γ, rfl⟩ := hlg_surj σ
      rw [hι'', QuotientGroup.eq_one_iff, ← hlg_ker] at hσ
      exact hσ
    · intro q
      obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨levelGal L F'' hLF'' γ, hι'' γ⟩
  let e : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) ≃* (↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype) := MulEquiv.ofBijective ι'' hι_bij
  have he : ∀ σ, e σ = ι'' σ := fun _ => rfl
  let eInv : (↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype) →* (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) := e.symm.toMonoidHom
  have heInv : ∀ q, ι'' (eInv q) = q := fun q => by
    change e (e.symm q) = q
    exact e.apply_symm_apply q
  have heInv' : ∀ σ, eInv (ι'' σ) = σ := fun σ => by
    change e.symm (e σ) = σ
    exact e.symm_apply_apply σ

  let φE : ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) ≃ₗ[ℤ] (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S)) := LinearEquiv.ofBijective φ''.hom.toLinearMap hφ''
  have hφE : ∀ m, φE m = φ''.hom m := fun _ => rfl
  have hφ''eq : ∀ (σ : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF''))) (m : ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      φ''.hom ((((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype))).ρ (ι'' σ) m) = ((NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S))).ρ σ (φ''.hom m) := fun σ m =>
    Rep.hom_comm_apply φ'' σ m
  let ψ : Rep.res eInv (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S)) ⟶ ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) :=
    Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ φE.symm.toLinearMap (fun q y => by
      change φE.symm (((NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S))).ρ (eInv q) y) = (((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype))).ρ q (φE.symm y)
      apply φE.injective
      rw [LinearEquiv.apply_symm_apply, hφE, ← heInv q, hφ''eq, heInv, ← hφE, LinearEquiv.apply_symm_apply]))
  have hψ : ∀ y, φ''.hom (ψ.hom y) = y := fun y => by
    change φE (φE.symm y) = y
    exact φE.apply_symm_apply y

  let f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) := mapCocycles₂ eInv ψ g
  have hHf : H2π _ f = (groupCohomology.map eInv ψ 2).hom (H2π _ g) := by
    change _ = (H2π _ ≫ groupCohomology.map eInv ψ 2).hom g
    rw [H2π_comp_map]
    rfl

  have key : (groupCohomology.map ι'' (φ'' ≫ j'') 2) (H2π _ f) = (groupCohomology.map (MonoidHom.id _) j'' 2) (H2π _ g) := by
    change (groupCohomology.map ι'' (φ'' ≫ j'') 2).hom (H2π _ f) = (groupCohomology.map (MonoidHom.id _) j'' 2).hom (H2π _ g)
    rw [hHf, map_map_apply]
    apply map_congr_apply
    · exact MonoidHom.ext fun σ => heInv' σ
    · intro y
      change j''.hom (φ''.hom (ψ.hom y)) = j''.hom y
      rw [hψ]

  let a₀ := continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F'' hF'' (H2π _ f)
  have ha₀ : (p ^ k : ℤ) • a₀ = 0 := by
    change (p ^ k : ℤ) • continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F'' hF'' (H2π _ f) = 0
    rw [← map_zsmul, hHf, ← map_zsmul, hk, map_zero, map_zero]
  have hamem : a₀ ∈ Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)) :=
    (Submodule.mem_torsion'_iff _ _).2 ⟨⟨(p ^ k : ℤ), k, by push_cast; rfl⟩, ha₀⟩
  refine ⟨⟨a₀, hamem⟩, fun v => ?_⟩

  refine ⟨F'', hLF'', inferInstance, inferInstance, inferInstance, hF'', ι'', hι'', φ'', hφ'', hφ''val, D'', inferInstance, hactI'',
    j'', hj'', f, rfl, ?_⟩
  rw [key]
  exact ht v

end S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep
end P2MW
export P2MW.S_NumberField_LevelArith_exists_forall_hasBrauerLocalInvAt_of_cocycles_sUnitsRep (solution)
