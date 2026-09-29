-- Prove2me | solution 1 for NumberField.LevelArith.map_principalIdele_H2pi_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cdfe6c78-990e-5e0d-a4a7-6d0a889b55c4

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
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_NumberField_LevelArith_levelGal_surjective_and_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_map_principalIdele_H2pi_eq_zero_of_le

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

namespace EmbAux

universe w u v

noncomputable def homOfAddMonoidHom {k : Type u} {G : Type v} [CommRing k] [Group G] (A B : Rep.{w} k G)
    (f : A →+ B) (hsmul : ∀ (c : k) (x : A), f (c • x) = c • f x)
    (hG : ∀ (g : G) (x : A), f (A.ρ g x) = B.ρ g (f x)) : A ⟶ B :=
  Rep.ofHom
    { toFun := f
      map_add' := f.map_add
      map_smul' := hsmul
      isIntertwining' := fun g => LinearMap.ext (hG g) }

theorem homOfAddMonoidHom_hom_apply {k : Type u} {G : Type v} [CommRing k] [Group G] (A B : Rep.{w} k G)
    (f : A →+ B) (hsmul : ∀ (c : k) (x : A), f (c • x) = c • f x)
    (hG : ∀ (g : G) (x : A), f (A.ρ g x) = B.ρ g (f x)) (x : A) :
    (homOfAddMonoidHom A B f hsmul hG).hom x = f x := by
  unfold homOfAddMonoidHom
  erw [Rep.hom_ofHom]
  rfl

end EmbAux

noncomputable section

namespace ResAux

section Gal

variable (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F) (hLF : L ≤ F)

def resGal (σ : ↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) :
    ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF) :=
  { (σ : ↥(levelField L' F hL'F) ≃+* ↥(levelField L' F hL'F)) with
    commutes' := fun c => by
      apply Subtype.ext
      exact congrArg Subtype.val (σ.commutes ⟨(c : AlgebraicClosure ℚ), hLL' c.2⟩) }

theorem resGal_apply_coe (σ : ↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (x : ↥(levelField L F hLF)) :
    ((resGal L L' F hLL' hL'F hLF σ x : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) =
      ((σ (x : ↥(levelField L' F hL'F)) : ↥(levelField L' F hL'F)) : AlgebraicClosure ℚ) := rfl

def resGalHom : (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) →* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) where
  toFun := resGal L L' F hLL' hL'F hLF
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

theorem resGalHom_apply (σ : ↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (x : ↥(levelField L F hLF)) :
    resGalHom L L' F hLL' hL'F hLF σ x = σ x := rfl

theorem resGalHom_levelGal [Normal ↥L ↥(levelField L F hLF)] [Normal ↥L' ↥(levelField L' F hL'F)] (γ : ↥L'.fixingSubgroup) :
    resGalHom L L' F hLL' hL'F hLF (levelGal L' F hL'F γ) =
      levelGal L F hLF ⟨(γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hLL' γ.2⟩ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [levelGal_apply_coe]
  exact levelGal_apply_coe L' F hL'F γ x

end Gal

section Descent

variable (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F) (hLF : L ≤ F)
  [FiniteDimensional ℚ ↥F]

def comapDescent (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF)) :
    IdeleGaloisDescent (𝓞 ↥(levelField L' F hL'F)) ↥L' ↥(levelField L' F hL'F) where
  act := D.act.comp (resGalHom L L' F hLL' hL'F hLF)
  compat g x := D.compat (resGalHom L L' F hLL' hL'F hLF g) x
  continuous_act g := D.continuous_act (resGalHom L L' F hLL' hL'F hLF g)

theorem unitsAct_eq_unitsAct_resGalHom
    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    (D' : IdeleGaloisDescent (𝓞 ↥(levelField L' F hL'F)) ↥L' ↥(levelField L' F hL'F))
    (g : ↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (x : (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ) :
    D'.unitsAct g x = D.unitsAct (resGalHom L L' F hLL' hL'F hLF g) x := by
  have h : D' = comapDescent L L' F hLL' hL'F hLF D :=
    @Subsingleton.elim _ (M4aHerbrand.subsingleton_ideleGaloisDescent _ _ _) _ _
  subst h
  rfl

end Descent

end ResAux

end

noncomputable section

namespace ResAux

section Apply

universe u

variable {k G H H₀ H' : Type u} [CommRing k] [Group G] [Group H] [Group H₀] [Group H']

theorem mapCocycles₂_comp_eq_of_forall
    {A : Rep k H} {C B₀ : Rep k H₀} {A₁ : Rep k H'} {C₁ B : Rep k G}
    (F : H₀ →* H) (R : G →* H₀) (φ : Rep.res F A ⟶ C) (j : C ⟶ B₀) (Θ : Rep.res R B₀ ⟶ B)
    (F₁ : G →* H') (φ₁ : Rep.res F₁ A₁ ⟶ C₁) (j₁ : C₁ ⟶ B) (x : cocycles₂ A) (x₁ : cocycles₂ A₁)
    (e : B₀ → B) (hΘ : ∀ y, Θ.hom y = e y)
    (hpt : ∀ g h : G, e (j.hom (φ.hom (x (F (R g), F (R h))))) = j₁.hom (φ₁.hom (x₁ (F₁ g, F₁ h)))) :
    mapCocycles₂ (F.comp R) ((Rep.resFunctor R).map (φ ≫ j) ≫ Θ) x = mapCocycles₂ F₁ (φ₁ ≫ j₁) x₁ :=
  cocycles₂_ext fun g h => by
    show Θ.hom (j.hom (φ.hom (x (F (R g), F (R h))))) = j₁.hom (φ₁.hom (x₁ (F₁ g, F₁ h)))
    rw [hΘ]
    exact hpt g h

end Apply

end ResAux

end

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥L'] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] [IsGalois ↥L' ↥(levelField L' F hL'F)] [Normal ↥L' ↥(levelField L' F hL'F)] (hF : F.IsUnramifiedOutside S)

    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
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

    (ι' : (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) →* (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))
    (hι' : ∀ g : ↥L'.fixingSubgroup, ι' (levelGal L' F hL'F g) = (g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)))
    (φ' : Rep.res ι' ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S))
    (hφ' : Function.Bijective φ'.hom)
    (hφval' : ∀ x, ((NumberField.SUnits.val ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S) (φ'.hom x) : ↥(levelField L' F hL'F)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L' (x.1 : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))

    (D' : IdeleGaloisDescent (𝓞 ↥(levelField L' F hL'F)) ↥L' ↥(levelField L' F hL'F))
    [MulDistribMulAction (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ]
    (hactI' : ∀ (g : ↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (x : (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ), g • x = D'.unitsAct g x)
    (j' : NumberField.SUnits.sUnitsRep ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ)
    (hj' : ∀ y, Additive.toMul (j'.hom y) =
      Units.map (algebraMap ↥(levelField L' F hL'F) (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F)) : ↥(levelField L' F hL'F) →* AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))
        (NumberField.SUnits.val ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S) y))

    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hx : (groupCohomology.map ι (φ ≫ j) 2) (H2π _ f) = 0)
    (f' : cocycles₂ ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)))
    (hff' : ∀ (g h : ↥L'.fixingSubgroup) (g₀ h₀ : ↥L.fixingSubgroup),
      ((g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((h₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((sUnitsMaxRep.val S L' ((f' ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L ((f ((g₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) :
    (groupCohomology.map ι' (φ' ≫ j') 2) (groupCohomology.H2π _ f') = 0 := by
  classical

  have hG : ∀ (g : (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F))) (x : Rep.res (ResAux.resGalHom L L' F hLL' hL'F hLF) (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)),
      (AddMonoidHom.id (Additive (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)) ((Rep.res (ResAux.resGalHom L L' F hLL' hL'F hLF) (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).ρ g x)
        = (Rep.ofMulDistribMulAction (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ).ρ g (AddMonoidHom.id (Additive (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) x) := by
    intro g x
    show Additive.ofMul (((ResAux.resGalHom L L' F hLL' hL'F hLF) g) • @Additive.toMul (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ x) = Additive.ofMul (g • @Additive.toMul (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ x)
    rw [hactI, hactI', ResAux.unitsAct_eq_unitsAct_resGalHom L L' F hLL' hL'F hLF D D']
    rfl
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Rep.res (ResAux.resGalHom L L' F hLL' hL'F hLF) (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶ (Rep.ofMulDistribMulAction (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ), ∀ x, Θ.hom x = x :=
    ⟨_, EmbAux.homOfAddMonoidHom_hom_apply (Rep.res (ResAux.resGalHom L L' F hLL' hL'F hLF) (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)) (Rep.ofMulDistribMulAction (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ) (AddMonoidHom.id _) (fun _ _ => rfl) hG⟩

  have h1 : (groupCohomology.map (ι.comp (ResAux.resGalHom L L' F hLL' hL'F hLF)) ((Rep.resFunctor (ResAux.resGalHom L L' F hLL' hL'F hLF)).map (φ ≫ j) ≫ Θ) 2) (H2π _ f) = 0 := by
    rw [groupCohomology.map_comp, ConcreteCategory.comp_apply]
    erw [hx]
    exact map_zero _
  rw [groupCohomology.H2π_comp_map_apply] at h1 ⊢

  obtain ⟨hsurj', -⟩ := NumberField.LevelArith.levelGal_surjective_and_ker L' F hL'F
  have hc : mapCocycles₂ (ι.comp (ResAux.resGalHom L L' F hLL' hL'F hLF)) ((Rep.resFunctor (ResAux.resGalHom L L' F hLL' hL'F hLF)).map (φ ≫ j) ≫ Θ) f = mapCocycles₂ ι' (φ' ≫ j') f' := by
    refine ResAux.mapCocycles₂_comp_eq_of_forall ι (ResAux.resGalHom L L' F hLL' hL'F hLF) φ j Θ ι' φ' j' f f' (fun y => y) hΘ ?_
    intro g' h'
    obtain ⟨g, hg⟩ := hsurj' g'
    obtain ⟨h, hh⟩ := hsurj' h'
    let g₀ : ↥L.fixingSubgroup := ⟨(g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hLL' g.2⟩
    let h₀ : ↥L.fixingSubgroup := ⟨(h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hLL' h.2⟩
    have e1 : (ι ((ResAux.resGalHom L L' F hLL' hL'F hLF) g'), ι ((ResAux.resGalHom L L' F hLL' hL'F hLF) h')) = ((g₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) := by
      rw [← hg, ← hh, ResAux.resGalHom_levelGal, ResAux.resGalHom_levelGal, hι, hι]
    have e2 : (ι' g', ι' h') = ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) := by
      rw [← hg, ← hh, hι', hι']
    have hv : NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom (f ((g₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))))
        = NumberField.SUnits.val ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S) (φ'.hom (f' ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))))) :=
      Units.ext (Subtype.ext ((hφval _).trans ((hff' g h g₀ h₀ rfl rfl).symm.trans (hφval' _).symm)))
    have e3 : j.hom (φ.hom (f ((g₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))))) = j'.hom (φ'.hom (f' ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))))) :=
      Additive.toMul.injective ((hj _).trans ((congrArg (Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) :
        ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) hv).trans (hj' _).symm))
    exact (congrArg (fun p => j.hom (φ.hom (f p))) e1).trans
      (e3.trans (congrArg (fun p => j'.hom (φ'.hom (f' p))) e2).symm)
  exact (congrArg (H2π (Rep.ofMulDistribMulAction (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ)) hc).symm.trans h1

end S_NumberField_LevelArith_map_principalIdele_H2pi_eq_zero_of_le
end P2MW
export P2MW.S_NumberField_LevelArith_map_principalIdele_H2pi_eq_zero_of_le (solution)
