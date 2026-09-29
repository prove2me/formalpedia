-- Prove2me | solution 1 for M4aHerbrand.map_inclusion_map_subtype_eq_map_inclusion_map_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8118b095-1f27-505c-8d36-81407c4c5683

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_map_inclusion_map_subtype_eq_map_inclusion_map_decomp
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_map_inclusion_map_subtype_eq_map_inclusion_map_decomp.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart"
namespace CoordFactor
p2m_open "M4aHerbrand"

theorem map_congr_hom {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    (f₁ f₂ : G →* H) (h : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ B) (φ₂ : Rep.res f₂ A ⟶ B)
    (hφ : φ₁.hom.toLinearMap = φ₂.hom.toLinearMap) (n : ℕ) :
    groupCohomology.map f₁ φ₁ n = groupCohomology.map f₂ φ₂ n := by
  subst h
  have : φ₁ = φ₂ := Rep.hom_ext (Representation.IntertwiningMap.ext hφ)
  rw [this]

end M4aHerbrand.CoordFactor

theorem solution
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] [IsGalois E M]
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (S : Subgroup (M ≃ₐ[E] M)) (W : HeightOneSpectrum (𝓞 M))
    (prH : Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ S))
          (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ))
    (hprH : ∀ x : (AdeleRing (𝓞 M) M)ˣ, prH.hom (Additive.ofMul x) = Additive.ofMul (finPart W x))
    (prM : Rep.res (NumberField.PlaceDecomp.decomp E M W).subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hprM : ∀ x : (AdeleRing (𝓞 M) M)ˣ, prM.hom (Additive.ofMul x) = Additive.ofMul (finPart W x))
    (n : ℕ) (x : groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) n) :
    (groupCohomology.map (Subgroup.inclusion (inf_le_left : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ S)) prH n).hom
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ))) n).hom x) =
      (groupCohomology.map (Subgroup.inclusion (inf_le_right : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
          (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
            (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ))) n).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp E M W).subtype prM n).hom x) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← groupCohomology.map_comp,
    ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← groupCohomology.map_comp]
  congr 2
  refine M4aHerbrand.CoordFactor.map_congr_hom _ _ (MonoidHom.ext fun _ => rfl) _ _ ?_ n
  apply LinearMap.ext
  intro a
  change prH.hom a = prM.hom a
  exact (hprH (Additive.toMul a)).trans (hprM (Additive.toMul a)).symm

end S_M4aHerbrand_map_inclusion_map_subtype_eq_map_inclusion_map_decomp
end P2MW
export P2MW.S_M4aHerbrand_map_inclusion_map_subtype_eq_map_inclusion_map_decomp (solution)
