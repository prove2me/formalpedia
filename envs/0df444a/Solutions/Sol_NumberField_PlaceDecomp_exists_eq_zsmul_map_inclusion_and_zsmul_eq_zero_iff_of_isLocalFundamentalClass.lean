-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_eq_zsmul_map_inclusion_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9d1f8f86-1758-5cd2-828a-a5c0f705a818

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_exists_eq_zsmul_map_subtype_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass
import Theorems.Thm_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_eq_zsmul_map_inclusion_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory NumberField P2MW.S_NumberField_PlaceDecomp_exists_eq_zsmul_map_inclusion_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_eq_zsmul_map_inclusion_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass.NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.exists_eq_zsmul_map_subtype_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp exists_eq_zsmul_map_subtype_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass"
namespace P2IProof
p2m_open "NumberField.PlaceDecomp NumberField"
open CategoryTheory

theorem map_eq_map_of_hom_eq {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ B) (φ₂ : Rep.res f₂ A ⟶ B)
    (hφ : ∀ a : A, φ₁.hom a = φ₂.hom a) (n : ℕ) :
    groupCohomology.map f₁ φ₁ n = groupCohomology.map f₂ φ₂ n := by
  subst h
  obtain rfl : φ₁ = φ₂ := by
    ext a
    exact hφ a
  rfl

theorem map_map_eq_map {k G H K : Type} [CommRing k] [Group G] [Group H] [Group K] {A : Rep k K} {B : Rep k H} {C : Rep k G}
    (f : H →* K) (φ : Rep.res f A ⟶ B) (g : G →* H) (ψ : Rep.res g B ⟶ C) (l : G →* K) (χ : Rep.res l A ⟶ C)
    (hgrp : f.comp g = l) (hval : ∀ a : A, ψ.hom (φ.hom a) = χ.hom a) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map g ψ n).hom ((groupCohomology.map f φ n).hom x) = (groupCohomology.map l χ n).hom x := by
  have h1 := congrArg (fun T => T.hom x) (groupCohomology.map_comp f g φ ψ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [← h1]
  exact congrArg (fun (T : groupCohomology A n ⟶ groupCohomology C n) => T.hom x) (map_eq_map_of_hom_eq hgrp _ _ hval n)

end NumberField.PlaceDecomp.P2IProof

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K))
    (hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E K w))
    (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ]
    (Φ : w.adicCompletion K ≃+* L)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L y = algebraMap ℚ_[q] L y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L (↥(NumberField.PlaceDecomp.decomp E K w)) K₀)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (_ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E K w)) K₀ u)
    (H : Subgroup (K ≃ₐ[E] K)) :
    (∀ z : groupCohomology (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E K w) ≤ (NumberField.PlaceDecomp.decomp E K w)))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)) 2,
      ∃ m : ℤ, z = m • (groupCohomology.map (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E K w) ≤ (NumberField.PlaceDecomp.decomp E K w)))
        (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E K w) ≤ (NumberField.PlaceDecomp.decomp E K w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ))) 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u)) ∧
    (∀ m : ℤ, m • (groupCohomology.map (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E K w) ≤ (NumberField.PlaceDecomp.decomp E K w)))
        (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E K w) ≤ (NumberField.PlaceDecomp.decomp E K w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ))) 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u) = 0 ↔
        (Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E K w)) : ℤ) ∣ m) := by
  open NumberField.PlaceDecomp.P2IProof in
  rename_i _hq _hfinL _actL _actU hQ hU hΦ _hfinK hB hθ hu

  let S' : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w) := (H ⊓ (NumberField.PlaceDecomp.decomp E K w)).subgroupOf (NumberField.PlaceDecomp.decomp E K w)
  let e : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E K w)) ≃* ↥S' := (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E K w) ≤ (NumberField.PlaceDecomp.decomp E K w))).symm
  let φ : Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E K w) ≤ (NumberField.PlaceDecomp.decomp E K w)))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
      ≅ Rep.res e.toMonoidHom (Rep.res S'.subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)) :=
    { hom := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
      inv := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
      hom_inv_id := rfl
      inv_hom_id := rfl }
  obtain ⟨ψ, hψ⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv e _ _ φ 2
  obtain ⟨hgenS, hordS⟩ := NumberField.PlaceDecomp.exists_eq_zsmul_map_subtype_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass E K w hsolv q L Φ
    hQ hU hΦ K₀ hB θ hθ u hu S'

  have hR : ψ.symm ((groupCohomology.map S'.subtype (𝟙 (Rep.res S'.subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ))) 2).hom
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u))
      = ((groupCohomology.map (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E K w) ≤ (NumberField.PlaceDecomp.decomp E K w)))
        (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E K w) ≤ (NumberField.PlaceDecomp.decomp E K w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ))) 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u)) := by
    rw [hψ]
    exact map_map_eq_map S'.subtype (𝟙 _) e.toMonoidHom φ.inv _ (𝟙 _) (by ext; rfl) (fun _ => rfl) 2 _
  refine ⟨fun z => ?_, fun m => ?_⟩
  · obtain ⟨m, hm⟩ := hgenS (ψ z)
    refine ⟨m, ?_⟩
    rw [← hR, ← map_zsmul ψ.symm, ← hm, LinearEquiv.symm_apply_apply]
  · rw [Nat.card_congr e.toEquiv, ← hordS m, ← hR, ← map_zsmul ψ.symm, LinearEquiv.map_eq_zero_iff]

end S_NumberField_PlaceDecomp_exists_eq_zsmul_map_inclusion_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_eq_zsmul_map_inclusion_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass (solution)
