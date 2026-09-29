-- Prove2me | solution 1 for NumberField.LevelArith.exists_level_d_two_three_eq_of_restrict_coboundary_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3ac7ed74-1471-59f8-98c9-951653f6c6bd

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_GroupCohomology_CorestrictionFin
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Theorems.Thm_groupCohomology_Cores_exists_d_eq_corFin_resFin_sub_index_smul_three
import Theorems.Thm_groupCohomology_Cores_corFin_d
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_level_d_two_three_eq_of_restrict_coboundary_of_not_dvd

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

set_option maxHeartbeats 6400000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥L'] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (hcop : ¬ p ∣ Module.finrank ↥L ↥(levelField L L' hLL'))
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hf : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0)
    (k : ℕ) (b₀ : (Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hk : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f)
    (f' : (Fin 3 → (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)))
    (hff' : ∀ (g : Fin 3 → ↥L'.fixingSubgroup) (g₀ : Fin 3 → ↥L.fixingSubgroup),
        (∀ i, ((g₀ i : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = ((g i : ↥L'.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
        ((sUnitsMaxRep.val S L' ((f' (fun i => (g i : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L ((f (fun i => (g₀ i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (hcob : ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F') (_ : F ≤ F')
      (b' : (Fin 2 → (↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L').quotientToInvariants (F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))),
      ∀ g : Fin 3 → ↥L'.fixingSubgroup,
        ((f' (fun i => (g i : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : sUnitsMaxRep S L')
          = ((((inhomogeneousCochains ((sUnitsMaxRep S L').quotientToInvariants (F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))).d 2 3).hom b' (fun i => (g i : (↥L'.fixingSubgroup ⧸ F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L').quotientToInvariants (F'.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : sUnitsMaxRep S L')) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F') (_ : F ≤ F')
      (b : (Fin 2 → (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b (fun i => (g i : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  obtain ⟨F', hF', hGF', hFF', b', hb'⟩ := hcob
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
  let I := groupCohomology.cochainsMap πFF' j
  have hIcomm : ∀ (i k : ℕ) x, ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants U)).d i k).hom ((I.f i).hom x) =
      (I.f k).hom (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants UF)).d i k).hom x) := fun i k x =>
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (I.comm i k)) x
  let u : (Fin 3 → ↥L.fixingSubgroup ⧸ U) → (sUnitsMaxRep S L).quotientToInvariants U := (I.f 3).hom f
  let v : (Fin 2 → ↥L.fixingSubgroup ⧸ U) → (sUnitsMaxRep S L).quotientToInvariants U := (I.f 2).hom b₀
  have hu : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants U)).d 3 4).hom u = 0 := by
    show ((inhomogeneousCochains _).d 3 4).hom ((I.f 3).hom f) = 0
    rw [hIcomm, hf, map_zero]
  have hv : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants U)).d 2 3).hom v = (p ^ k : ℤ) • u := by
    show ((inhomogeneousCochains _).d 2 3).hom ((I.f 2).hom b₀) = (p ^ k : ℤ) • (I.f 3).hom f
    rw [hIcomm, hk, map_zsmul]

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
  have hcopH : Nat.Coprime H.index (p ^ k) := by
    rw [hHidx]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcop)).pow_right k

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
  let K := groupCohomology.cochainsMap (e.toMonoidHom : ↥H →* (↥L'.fixingSubgroup ⧸ U')) κ'
  have hKcomm : ∀ (i k : ℕ) x, ((inhomogeneousCochains (Rep.res H.subtype ((sUnitsMaxRep S L).quotientToInvariants U))).d i k).hom ((K.f i).hom x) =
      (K.f k).hom (((inhomogeneousCochains ((sUnitsMaxRep S L').quotientToInvariants U')).d i k).hom x) := fun i k x =>
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (K.comm i k)) x
  let c : (Fin 2 → ↥H) → (sUnitsMaxRep S L).quotientToInvariants U := (K.f 2).hom b'
  have hres : groupCohomology.Cores.resFin ((sUnitsMaxRep S L).quotientToInvariants U) 3 u =
      ((inhomogeneousCochains (Rep.res H.subtype ((sUnitsMaxRep S L).quotientToInvariants U))).d 2 3).hom c := by
    show _ = ((inhomogeneousCochains _).d 2 3).hom ((K.f 2).hom b')
    rw [hKcomm]
    funext h

    let γ' : Fin 3 → ↥L'.fixingSubgroup := fun i => (e (h i)).out
    have hγ' : (fun i => e (h i)) = fun i => (γ' i : ↥L'.fixingSubgroup ⧸ U') := funext fun i => (QuotientGroup.out_eq' _).symm
    have hh : ∀ i, (h i : ↥L.fixingSubgroup ⧸ U) = (QuotientGroup.mk (incl (γ' i)) : ↥L.fixingSubgroup ⧸ U) := fun i => by
      rw [← he (h i), congrFun hγ' i]; rfl
    apply Subtype.ext
    apply hvalinj

    change sUnitsMaxRep.val S L ((jlin (f (fun i => πFF' (H.subtype (h i))))) : sUnitsMaxRep S L) =
      sUnitsMaxRep.val S L ((κ ((((inhomogeneousCochains ((sUnitsMaxRep S L').quotientToInvariants U')).d 2 3).hom b')
        (fun i => e.toMonoidHom (h i)))) : sUnitsMaxRep S L)
    have hπ : (fun i => πFF' (H.subtype (h i))) = fun i => ((incl (γ' i) : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ UF) :=
      funext fun i => by rw [Subgroup.subtype_apply, hh i]; rfl
    have he' : (fun i => e.toMonoidHom (h i)) = fun i => (γ' i : ↥L'.fixingSubgroup ⧸ U') :=
      funext fun i => by rw [MulEquiv.coe_toMonoidHom]; exact congrFun hγ' i
    rw [hπ, he', hκ, ← hb' γ']
    exact Units.ext (hff' γ' (fun i => incl (γ' i)) (fun i => rfl)).symm

  obtain ⟨τ⟩ := (groupCohomology.Cores.Transversal.nonempty : Nonempty (groupCohomology.Cores.Transversal H))
  obtain ⟨b₁, hb₁, -⟩ := groupCohomology.Cores.exists_d_eq_corFin_resFin_sub_index_smul_three
    ((sUnitsMaxRep S L).quotientToInvariants U) H τ u hu
  rw [hres, groupCohomology.Cores.corFin_d] at hb₁
  have hD : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants U)).d 2 3).hom b₁ =
      ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants U)).d 2 3).hom
        (groupCohomology.Cores.corFin ((sUnitsMaxRep S L).quotientToInvariants U) τ 2 c) - H.index • u := hb₁
  clear hb₁
  obtain ⟨a, cc, hac⟩ := Nat.isCoprime_iff_coprime.2 hcopH
  have hac' : a * (H.index : ℤ) + cc * (p : ℤ) ^ k = 1 := by exact_mod_cast hac
  have hdb : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants U)).d 2 3).hom
      (a • (groupCohomology.Cores.corFin ((sUnitsMaxRep S L).quotientToInvariants U) τ 2 c - b₁) + cc • v) = u := by
    rw [map_add, map_zsmul, map_zsmul, map_sub, hv]
    have hidx : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants U)).d 2 3).hom
          (groupCohomology.Cores.corFin ((sUnitsMaxRep S L).quotientToInvariants U) τ 2 c) -
        ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants U)).d 2 3).hom b₁ = (H.index : ℤ) • u := by
      rw [hD, natCast_zsmul]
      abel
    rw [hidx, smul_smul, smul_smul, ← add_smul, hac', one_smul]
  refine ⟨F', hF', hGF', hFF', a • (groupCohomology.Cores.corFin ((sUnitsMaxRep S L).quotientToInvariants U) τ 2 c - b₁) + cc • v,
    fun g => ?_⟩
  rw [congrFun hdb (fun i => (g i : ↥L.fixingSubgroup ⧸ U))]
  rfl

end S_NumberField_LevelArith_exists_level_d_two_three_eq_of_restrict_coboundary_of_not_dvd
end P2MW
export P2MW.S_NumberField_LevelArith_exists_level_d_two_three_eq_of_restrict_coboundary_of_not_dvd (solution)
