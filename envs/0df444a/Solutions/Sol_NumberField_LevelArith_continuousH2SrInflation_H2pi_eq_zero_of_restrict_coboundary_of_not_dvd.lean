-- Prove2me | solution 1 for NumberField.LevelArith.continuousH2SrInflation_H2pi_eq_zero_of_restrict_coboundary_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/192b0cb2-70cc-53e5-8715-4621e1dc55ea

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
import Definitions.Def_GroupCohomology_Corestriction2
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Theorems.Thm_groupCohomology_eq_zero_of_map_res_two_eq_zero_of_coprime
import Theorems.Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_continuousH2SrInflation_H2pi_eq_zero_of_restrict_coboundary_of_not_dvd

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

set_option maxHeartbeats 6400000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥L'] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (hcop : ¬ p ∣ Module.finrank ↥L ↥(levelField L L' hLL'))
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (k : ℕ) (hk : (p ^ k : ℤ) • (H2π _ f) = 0)
    (f' : cocycles₂ ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)))
    (hff' : ∀ (g h : ↥L'.fixingSubgroup) (g₀ h₀ : ↥L.fixingSubgroup),
      ((g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((h₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((sUnitsMaxRep.val S L' ((f' ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L ((f ((g₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (hcob : ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ F') (_ : F ≤ F')
      (y : (↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype) →
        (sUnitsMaxRep S L').quotientToInvariants (F'.fixingSubgroup.comap L'.fixingSubgroup.subtype)),
      ∀ g h : ↥L'.fixingSubgroup,
        ((f' ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L')
          = (sUnitsMaxRep S L').ρ g (y (h : ↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))
            - (y ((g * h : ↥L'.fixingSubgroup) : ↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype) : sUnitsMaxRep S L')
            + y (g : ↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype)) :
    continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f) = 0 := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  obtain ⟨F', hF', hGF', hFF', y', hy'⟩ := hcob
  haveI := hGF'
  haveI : FiniteDimensional ℚ ↥F' := hF'.1
  haveI : Normal ℚ ↥F' := hGF'.to_normal

  let UF  : Subgroup ↥L.fixingSubgroup  := F.fixingSubgroup.comap L.fixingSubgroup.subtype
  let U   : Subgroup ↥L.fixingSubgroup  := F'.fixingSubgroup.comap L.fixingSubgroup.subtype
  let UF' : Subgroup ↥L'.fixingSubgroup := F.fixingSubgroup.comap L'.fixingSubgroup.subtype
  let U'  : Subgroup ↥L'.fixingSubgroup := F'.fixingSubgroup.comap L'.fixingSubgroup.subtype
  haveI : U.FiniteIndex := groupCohomology.finiteIndex_comap_fixingSubgroup L.fixingSubgroup.subtype F'
  haveI : Finite (↥L.fixingSubgroup ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  have hΓ : L'.fixingSubgroup ≤ L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hLL'
  let incl : ↥L'.fixingSubgroup →* ↥L.fixingSubgroup := Subgroup.inclusion hΓ
  have hUU_F : U ≤ UF := groupCohomology.comap_fixingSubgroup_antitone _ hFF'
  have hF'Γ' : F'.fixingSubgroup ≤ L'.fixingSubgroup := IntermediateField.fixingSubgroup_antitone (hL'F.trans hFF')

  have hvalinj : ∀ {x y : sUnitsMaxRep S L}, sUnitsMaxRep.val S L x = sUnitsMaxRep.val S L y → x = y :=
    fun h => Subtype.ext (Additive.toMul.injective h)
  have hcar : sUnitsMaxSubmodule S L' = sUnitsMaxSubmodule S L := by
    ext x
    rw [mem_sUnitsMaxSubmodule, mem_sUnitsMaxSubmodule, sUnitsMaxStable_eq_sUnitsMax, sUnitsMaxStable_eq_sUnitsMax]

  let πFF' : (↥L.fixingSubgroup ⧸ U) →* (↥L.fixingSubgroup ⧸ UF) := QuotientGroup.map _ _ (MonoidHom.id _) (by simpa using hUU_F)
  let jlin : ((sUnitsMaxRep S L).quotientToInvariants UF) →ₗ[ℤ] ((sUnitsMaxRep S L).quotientToInvariants U) :=
    { toFun := fun v => ⟨v.1, fun γ => v.2 ⟨γ.1, hUU_F γ.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let j : Rep.res πFF' ((sUnitsMaxRep S L).quotientToInvariants UF) ⟶ (sUnitsMaxRep S L).quotientToInvariants U :=
    Rep.ofHom ⟨jlin, fun q => QuotientGroup.induction_on q fun γ => LinearMap.ext fun v => rfl⟩

  have hU'U : U' ≤ U.comap incl := fun γ h => h
  let θ : (↥L'.fixingSubgroup ⧸ U') →* (↥L.fixingSubgroup ⧸ U) := QuotientGroup.map _ _ incl hU'U
  let H : Subgroup (↥L.fixingSubgroup ⧸ U) := θ.range
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro q hq
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker] at hq
    change (QuotientGroup.mk (incl γ) : ↥L.fixingSubgroup ⧸ U) = 1 at hq
    rw [QuotientGroup.eq_one_iff] at hq ⊢
    exact hq
  let θH : (↥L'.fixingSubgroup ⧸ U') →* ↥H := θ.rangeRestrict
  have hθH : Function.Bijective θH := ⟨fun a b h => hθinj (congrArg Subtype.val h), θ.rangeRestrict_surjective⟩
  let e : ↥H ≃* (↥L'.fixingSubgroup ⧸ U') := (MulEquiv.ofBijective θH hθH).symm
  have he : ∀ h : ↥H, θ (e h) = (h : ↥L.fixingSubgroup ⧸ U) := fun h => by
    have := MulEquiv.apply_symm_apply (MulEquiv.ofBijective θH hθH) h
    exact congrArg Subtype.val this
  have hHidx : H.index = Module.finrank ↥L ↥(levelField L L' hLL') := by

    have hH : H = (incl.range).map (QuotientGroup.mk' U) := by
      apply le_antisymm
      · rintro _ ⟨q, rfl⟩
        obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
        exact ⟨incl γ, ⟨γ, rfl⟩, rfl⟩
      · rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
        exact ⟨(γ : ↥L'.fixingSubgroup ⧸ U'), rfl⟩
    have hUle : U ≤ incl.range := fun γ hγ => ⟨⟨γ.1, hF'Γ' hγ⟩, rfl⟩
    have h1 : H.index = incl.range.index := by
      rw [hH, Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.2 hUle, QuotientGroup.range_mk', Subgroup.index_top, mul_one]
    have h2 : incl.range = L'.fixingSubgroup.subgroupOf L.fixingSubgroup := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x.1, hx⟩, rfl⟩⟩
    have h3 : (L'.fixingSubgroup.subgroupOf L.fixingSubgroup).index * L.fixingSubgroup.index = L'.fixingSubgroup.index :=
      Subgroup.relIndex_mul_index hΓ
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index, ← IntermediateField.finrank_eq_fixingSubgroup_index,
      ← IntermediateField.finrank_bot_mul_relfinrank hLL', IntermediateField.relfinrank_eq_finrank_of_le hLL',
      mul_comm] at h3
    have h4 := Nat.eq_of_mul_eq_mul_left Module.finrank_pos h3
    rw [h1, h2, h4]
  have hcopH : H.index.Coprime p := by
    rw [hHidx]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcop)

  let κ : ((sUnitsMaxRep S L').quotientToInvariants U') →ₗ[ℤ] ((sUnitsMaxRep S L).quotientToInvariants U) :=
    { toFun := fun w => ⟨⟨(w.1).1, hcar ▸ (w.1).2⟩, fun γ => by
        have h0 := congrArg (sUnitsMaxRep.val S L') (w.2 ⟨⟨(γ.1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), hF'Γ' γ.2⟩, γ.2⟩)
        rw [MonoidHom.comp_apply, sUnitsMaxRep.val_ρ] at h0
        apply hvalinj
        rw [MonoidHom.comp_apply, sUnitsMaxRep.val_ρ]
        exact h0⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hκ : ∀ w, sUnitsMaxRep.val S L (κ w : sUnitsMaxRep S L) = sUnitsMaxRep.val S L' (w : sUnitsMaxRep S L') :=
    fun _ => rfl
  let κ' : Rep.res (e.toMonoidHom : ↥H →* (↥L'.fixingSubgroup ⧸ U')) ((sUnitsMaxRep S L').quotientToInvariants U') ⟶
      Rep.res H.subtype ((sUnitsMaxRep S L).quotientToInvariants U) :=
    Rep.ofHom ⟨κ, fun h => LinearMap.ext fun w => by
      obtain ⟨γ', hγ'⟩ := QuotientGroup.mk_surjective (e h)
      have hh : (h : ↥L.fixingSubgroup ⧸ U) = (QuotientGroup.mk (incl γ') : ↥L.fixingSubgroup ⧸ U) := by
        rw [← he h, ← hγ']; rfl
      apply Subtype.ext
      apply hvalinj
      change sUnitsMaxRep.val S L (κ (((sUnitsMaxRep S L').quotientToInvariants U').ρ (e.toMonoidHom h) w) : sUnitsMaxRep S L) =
        sUnitsMaxRep.val S L ((((sUnitsMaxRep S L).quotientToInvariants U).ρ (H.subtype h) (κ w)) : sUnitsMaxRep S L)
      rw [MulEquiv.coe_toMonoidHom, ← hγ', Subgroup.subtype_apply, hh]
      rfl⟩
  have hκ' : ∀ w, (κ'.hom w : sUnitsMaxRep S L) = (κ w : sUnitsMaxRep S L) := fun _ => rfl

  let fi : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants U) := (groupCohomology.mapCocycles₂ πFF' j).hom f
  have hpfi : p ^ k • H2π _ fi = 0 := by
    have := congrArg (groupCohomology.map πFF' j 2).hom hk
    rw [map_zsmul, map_zero, groupCohomology.H2π_comp_map_apply] at this
    rw [← natCast_zsmul]
    exact_mod_cast this

  have hEinj : Function.Injective (fun z : sUnitsMaxRep S L => (z.1 : Additive (AlgebraicClosure ℚ)ˣ)) := fun a b h => Subtype.ext h
  have hresH : (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype ((sUnitsMaxRep S L).quotientToInvariants U))) 2).hom
      (H2π _ fi) = 0 := by
    rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_eq_zero_iff]
    refine ⟨fun h => κ (y' (e h)), funext fun hh => ?_⟩
    obtain ⟨h₁, h₂⟩ := hh
    change ((((sUnitsMaxRep S L).quotientToInvariants U).ρ (h₁ : ↥L.fixingSubgroup ⧸ U) (κ (y' (e h₂))) - κ (y' (e (h₁ * h₂))) + κ (y' (e h₁)) :
        (sUnitsMaxRep S L).quotientToInvariants U) = jlin (f (πFF' (h₁ : ↥L.fixingSubgroup ⧸ U), πFF' (h₂ : ↥L.fixingSubgroup ⧸ U))))
    obtain ⟨q₁, rfl⟩ := e.symm.surjective h₁
    obtain ⟨q₂, rfl⟩ := e.symm.surjective h₂
    obtain ⟨γ₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨γ₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    rw [← map_mul e.symm, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    apply hEinj
    simp only [AddMemClass.coe_add, AddSubgroupClass.coe_sub]
    have key := congrArg (fun z : sUnitsMaxRep S L' => (z.1 : Additive (AlgebraicClosure ℚ)ˣ)) (hy' γ₁ γ₂)
    simp only [AddMemClass.coe_add, AddSubgroupClass.coe_sub] at key
    have h4 : ((((f' ((γ₁ : ↥L'.fixingSubgroup ⧸ UF'), (γ₂ : ↥L'.fixingSubgroup ⧸ UF')) : (sUnitsMaxRep S L').quotientToInvariants UF') : sUnitsMaxRep S L').1) : Additive (AlgebraicClosure ℚ)ˣ) =
        ((((f (((incl γ₁ : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ UF), ((incl γ₂ : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ UF)) : (sUnitsMaxRep S L).quotientToInvariants UF) : sUnitsMaxRep S L).1) : Additive (AlgebraicClosure ℚ)ˣ) :=
      congrArg Additive.ofMul (Units.ext (hff' γ₁ γ₂ (incl γ₁) (incl γ₂) rfl rfl))
    rw [h4] at key
    exact key.symm

  have hzero := groupCohomology.eq_zero_of_map_res_two_eq_zero_of_coprime
    ((sUnitsMaxRep S L).quotientToInvariants U) H hcopH (H2π _ fi) hpfi hresH
  rw [groupCohomology.H2π_eq_zero_iff] at hzero
  obtain ⟨y, hy⟩ := hzero

  have hsm : ∀ m : sUnitsMaxRep S L, ∃ Fm : IntermediateField ℚ (AlgebraicClosure ℚ), Fm.IsUnramifiedOutside S ∧
      ∀ s : ↥L.fixingSubgroup, L.fixingSubgroup.subtype s ∈ Fm.fixingSubgroup → (sUnitsMaxRep S L).ρ s m = m := by
    intro m
    obtain ⟨Fm, hFm, hmF⟩ := (sUnitsMaxStable_le S L m.2).1
    refine ⟨Fm, hFm, fun s hs => ?_⟩
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs _ hmF
    apply hvalinj
    rw [sUnitsMaxRep.val_ρ]
    exact Units.ext hfix
  refine (groupCohomology.continuousH2SrInflation_H2pi_eq_zero_iff L.fixingSubgroup.subtype S (sUnitsMaxRep S L) hsm F hF f).2
    ⟨F', hF', hGF', hFF', y, fun g h => ?_⟩
  have hgh := congrFun hy ((g : ↥L.fixingSubgroup ⧸ U), (h : ↥L.fixingSubgroup ⧸ U))
  change ((((sUnitsMaxRep S L).quotientToInvariants U).ρ (g : ↥L.fixingSubgroup ⧸ U) (y (h : ↥L.fixingSubgroup ⧸ U)) -
      y ((g : ↥L.fixingSubgroup ⧸ U) * (h : ↥L.fixingSubgroup ⧸ U)) + y (g : ↥L.fixingSubgroup ⧸ U) :
        (sUnitsMaxRep S L).quotientToInvariants U) = jlin (f (πFF' (g : ↥L.fixingSubgroup ⧸ U), πFF' (h : ↥L.fixingSubgroup ⧸ U)))) at hgh
  have hgh' := congrArg Subtype.val hgh
  simp only [AddMemClass.coe_add, AddSubgroupClass.coe_sub] at hgh'
  exact hgh'.symm

end S_NumberField_LevelArith_continuousH2SrInflation_H2pi_eq_zero_of_restrict_coboundary_of_not_dvd
end P2MW
export P2MW.S_NumberField_LevelArith_continuousH2SrInflation_H2pi_eq_zero_of_restrict_coboundary_of_not_dvd (solution)
