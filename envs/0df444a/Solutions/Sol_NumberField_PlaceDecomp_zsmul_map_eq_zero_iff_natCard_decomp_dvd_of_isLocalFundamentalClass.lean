-- Prove2me | solution 1 for NumberField.PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/92032073-4719-509b-a360-8254ead954f0

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass
p2m_attr_erase "simp" "groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField P2MW.S_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass.NumberField.PlaceDecomp"

set_option linter.unusedSectionVars false

namespace NumberField
p2m_export "NumberField" "PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceDecomp.faithfulSMul_decomp"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp coe_smul_units faithfulSMul_decomp"
namespace OrdProof
p2m_open "NumberField.PlaceDecomp NumberField"

section kernel
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (w : HeightOneSpectrum (𝓞 K))
    (hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E K w))
    (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K w) L] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L)ˣ]
    (Φ : w.adicCompletion K ≃+* L)
    (h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L y = algebraMap ℚ_[q] L y)
    (h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L))
    (h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (base : ExtCitation.LocalLevel.IsBase q L ↥(NumberField.PlaceDecomp.decomp E K w) K₀)
    (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L)ˣ ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ)
    (hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L)ˣ))
    (hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L ↥(NumberField.PlaceDecomp.decomp E K w) K₀ u)

include h3 in

theorem faithfulSMul_layer : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E K w) L := by
  haveI : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K) := NumberField.PlaceDecomp.faithfulSMul_decomp E K w
  exact ⟨fun {g₁ g₂} h => FaithfulSMul.eq_of_smul_eq_smul (α := w.adicCompletion K) fun y => Φ.injective (by rw [h3 g₁ y, h3 g₂ y]; exact h _)⟩

include hsolv h1 h2 h3 base hu in

theorem zsmul_eq_zero_iff (c : ℤ) : c • u = 0 ↔ (Nat.card ↥(NumberField.PlaceDecomp.decomp E K w) : ℤ) ∣ c := by
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  haveI : Finite (K ≃ₐ[E] K) := inferInstance
  letI : Fintype ↥(NumberField.PlaceDecomp.decomp E K w) := Fintype.ofFinite _
  letI : Fintype (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)) := Fintype.ofFinite _
  haveI := faithfulSMul_layer E K w q L Φ h3
  obtain ⟨-, hcard, hspan⟩ :=
    ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
      q L (↥(NumberField.PlaceDecomp.decomp E K w)) h1 h2 hsolv K₀ base u hu
  set r := (groupCohomology.map (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)).subtype
    (𝟙 (Rep.res (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L)ˣ))) 2).hom with hr

  have hres_inj : Function.Injective r := by
    let eT : ↥(NumberField.PlaceDecomp.decomp E K w) →* ↥(⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))) := (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))) ≃* ↥(NumberField.PlaceDecomp.decomp E K w)).symm.toMonoidHom
    have key : groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2 ≫
        groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ)))) 2 = 𝟙 _ := by
      rw [← groupCohomology.map_comp]
      exact groupCohomology.map_id (B := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ)) (n := 2)
    have hleft : ∀ y : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ),
        (groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ)))) 2).hom
          ((groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2).hom y) = y := by
      intro y
      have hy := congrArg (fun T => (ModuleCat.Hom.hom T) y) key
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hy
      exact hy
    exact Function.LeftInverse.injective hleft
  have hy : AddSubgroup.zmultiples (r u) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span ℤ {r u} := by rw [hr, hspan ⊤]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨a, by rw [← ha]; exact (int_smul_eq_zsmul _ a (r u)).symm⟩
  have hord : addOrderOf (r u) = Nat.card ↥(NumberField.PlaceDecomp.decomp E K w) := by
    rw [← Nat.card_zmultiples, hy, AddSubgroup.card_top, hcard ⊤, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)) ≃* ↥(NumberField.PlaceDecomp.decomp E K w)).toEquiv
  constructor
  · intro hc
    have : c • r u = 0 := by rw [← map_zsmul, hc, map_zero]
    rw [← hord]
    exact_mod_cast addOrderOf_dvd_iff_zsmul_eq_zero.mpr this
  · intro hc
    apply hres_inj
    rw [map_zsmul, map_zero]
    rw [← hord] at hc
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mp (by exact_mod_cast hc)

include h2 h3 hθ in

theorem exists_comp_eq_id :
    ∃ θ' : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) ⟶
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ), θ ≫ θ' = 𝟙 _ := by
  let ΦM : (w.adicCompletion K)ˣ →* (↥L)ˣ := Units.map Φ.toRingHom.toMonoidHom
  have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (m : (w.adicCompletion K)ˣ), ΦM (g • m) = g • ΦM m := by
    intro g m
    apply Units.ext
    rw [h2 g (ΦM m)]
    show Φ ((g • m : (w.adicCompletion K)ˣ) : (w.adicCompletion K)) = g • Φ (m : (w.adicCompletion K))
    rw [NumberField.PlaceDecomp.coe_smul_units, h3 g]
  refine ⟨M4aHerbrand.repHomOfMulEquivariant ΦM hΦM, ?_⟩
  refine Rep.hom_ext ?_
  ext z
  rw [Rep.hom_comp, Rep.hom_id]
  show (M4aHerbrand.repHomOfMulEquivariant ΦM hΦM).hom (θ.hom z) = z
  rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply]
  refine (congrArg Additive.ofMul ?_).trans (ofMul_toMul z)
  apply Units.ext
  show Φ ((Additive.toMul (θ.hom z) : (w.adicCompletion K)ˣ) : (w.adicCompletion K)) = ((Additive.toMul z : (↥L)ˣ) : ↥L)
  have h : ((Additive.toMul (θ.hom z) : (w.adicCompletion K)ˣ) : (w.adicCompletion K)) = Φ.symm ((Additive.toMul z : (↥L)ˣ) : ↥L) :=
    hθ (Additive.toMul z)
  rw [h]
  exact Φ.apply_symm_apply _

end kernel

end NumberField.PlaceDecomp.OrdProof

open NumberField.PlaceDecomp.OrdProof in

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K)) (hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E K w))
    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ]
    (Φ : w.adicCompletion K ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E K w)) K₀)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (_ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L'))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E K w)) K₀ u)
    (m : ℤ) :
    m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u = 0 ↔
      (Nat.card ↥(NumberField.PlaceDecomp.decomp E K w) : ℤ) ∣ m := by
  rename_i h1 h2 h3 _ base hθ hu
  obtain ⟨θ', hθ'⟩ := exists_comp_eq_id E K w q L' Φ h2 h3 θ hθ
  have hback : (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ' 2).hom
      ((groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ 2).hom u) = u := by
    have hc' := congrArg (fun T => (ModuleCat.Hom.hom T) u) (groupCohomology.map_id_comp θ θ' 2)
    simp only [hθ', groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at hc'
    exact hc'.symm
  rw [← zsmul_eq_zero_iff E K w hsolv q L' Φ h1 h2 h3 K₀ base u hu m]
  constructor
  · intro h
    rw [← hback, ← map_zsmul, h, map_zero]
  · intro h
    rw [← map_zsmul, h, map_zero]

end S_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass
end P2MW
export P2MW.S_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass (solution)
