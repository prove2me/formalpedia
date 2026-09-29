-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/64356ee3-d3fa-5465-9cb0-391c5000098f

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_groupCohomology_isZero_H1_and_natCard_H2_and_span_map_of_iso
import Theorems.Thm_groupCohomology_bijective_map_top_subtype
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_eq_zsmul_map_of_isLocalFundamentalClass
p2m_attr_erase "simp" "groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

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
    (z : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)) :
    ∃ m : ℤ, z = m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u := by
  rename_i _hq _hfinL _actL _actU hQ hU hΦ _hfinK hB hθ hu

  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E K w) L := ⟨fun {g₁} {g₂} h => by
    haveI := NumberField.PlaceDecomp.faithfulSMul_decomp E K w
    refine FaithfulSMul.eq_of_smul_eq_smul (α := w.adicCompletion K) fun y => Φ.injective ?_
    rw [hΦ, hΦ, h]⟩
  obtain ⟨h1, h2, h3⟩ := ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass q L
    ↥(NumberField.PlaceDecomp.decomp E K w) hQ hU hsolv K₀ hB u hu

  let f : (w.adicCompletion K)ˣ →* (↥L)ˣ := (Units.mapEquiv Φ.toMulEquiv).toMonoidHom
  have hfval : ∀ x : (w.adicCompletion K)ˣ, ((f x : (↥L)ˣ) : L) = Φ (x : w.adicCompletion K) := fun _ => rfl
  have hf : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (x : (w.adicCompletion K)ˣ), f (g • x) = g • f x := fun g x => by
    apply Units.ext
    rw [hU, hfval, hfval, NumberField.PlaceDecomp.coe_smul_units, hΦ]
  let θ' : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ := M4aHerbrand.repHomOfMulEquivariant f hf
  have key : ∀ v : (↥L)ˣ, θ'.hom (θ.hom (Additive.ofMul v)) = Additive.ofMul v := fun v => by
    have e1 : (Additive.toMul : Additive (↥L)ˣ ≃ (↥L)ˣ) (θ'.hom (θ.hom (Additive.ofMul v)))
        = f ((Additive.toMul : Additive (w.adicCompletion K)ˣ ≃ (w.adicCompletion K)ˣ) (θ.hom (Additive.ofMul v))) := rfl
    have e2 : f ((Additive.toMul : Additive (w.adicCompletion K)ˣ ≃ (w.adicCompletion K)ˣ) (θ.hom (Additive.ofMul v))) = v :=
      Units.ext (by rw [hfval, hθ v, RingEquiv.apply_symm_apply])
    apply (Additive.toMul : Additive (↥L)ˣ ≃ (↥L)ˣ).injective
    rw [e1, e2]
    rfl
  have key' : ∀ x : (w.adicCompletion K)ˣ, θ.hom (θ'.hom (Additive.ofMul x)) = Additive.ofMul x := fun x => by
    have e1 : θ'.hom (Additive.ofMul x) = Additive.ofMul (f x) := rfl
    have e2 : (((Additive.toMul : Additive (w.adicCompletion K)ˣ ≃ (w.adicCompletion K)ˣ) (θ.hom (Additive.ofMul (f x))) :
        (w.adicCompletion K)ˣ) : w.adicCompletion K) = x := by
      rw [hθ (f x), hfval, RingEquiv.symm_apply_apply]
    apply (Additive.toMul : Additive (w.adicCompletion K)ˣ ≃ (w.adicCompletion K)ˣ).injective
    rw [e1]
    exact Units.ext e2
  let e : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ ≅
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ :=
    { hom := θ
      inv := θ'
      hom_inv_id := by
        apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro a
        exact key ((Additive.toMul : Additive (↥L)ˣ ≃ (↥L)ˣ) a)
      inv_hom_id := by
        apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro a
        exact key' ((Additive.toMul : Additive (w.adicCompletion K)ˣ ≃ (w.adicCompletion K)ˣ) a) }
  obtain ⟨-, -, hspan⟩ := groupCohomology.isZero_H1_and_natCard_H2_and_span_map_of_iso _ _ e u h1 h2 h3

  have hbij := groupCohomology.bijective_map_top_subtype
    (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) 2
  have hmem : (groupCohomology.map (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)).subtype
      (𝟙 (Rep.res (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)).subtype
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ))) 2).hom z ∈
      Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)).subtype
        (𝟙 (Rep.res (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)).subtype
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ))) 2).hom
        ((groupCohomology.map (MonoidHom.id _) e.hom 2).hom u)} := by
    rw [hspan ⊤]; exact Submodule.mem_top
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨m, hbij.1 ?_⟩
  rw [map_zsmul, ← hm]
  exact int_smul_eq_zsmul _ m _

end S_NumberField_PlaceDecomp_exists_eq_zsmul_map_of_isLocalFundamentalClass
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_eq_zsmul_map_of_isLocalFundamentalClass (solution)
