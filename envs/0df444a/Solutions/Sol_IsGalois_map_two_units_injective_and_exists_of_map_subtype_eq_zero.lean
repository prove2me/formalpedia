-- Prove2me | solution 1 for IsGalois.map_two_units_injective_and_exists_of_map_subtype_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e4ef9cfb-e4a3-5244-8e01-be57b76b093a

import Mathlib
import Theorems.Thm_groupCohomology_inf_injective_and_exact_of_isZero_res
import Theorems.Thm_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv
import Theorems.Thm_groupCohomology_isZero_H1_res_units_of_smul_eq
import Theorems.Thm_IsGalois_exists_units_quotientToInvariants_iso_res_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsGalois_map_two_units_injective_and_exists_of_map_subtype_eq_zero

set_option autoImplicit false
open CategoryTheory groupCohomology

namespace M4aHerbrand
namespace UnitsInfRes

theorem main
    (E L M : Type) [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M]
    [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M]
    [MulDistribMulAction (L ≃ₐ[E] L) Lˣ]
    (hactL : ∀ (g : L ≃ₐ[E] L) (a : Lˣ), ((g • a : Lˣ) : L) = g (a : L))
    [MulDistribMulAction (M ≃ₐ[E] M) Mˣ]
    (hactM : ∀ (g : M ≃ₐ[E] M) (a : Mˣ), ((g • a : Mˣ) : M) = g (a : M))
    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L))
    (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y))
    (i : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ)
    (hi : ∀ a : Lˣ, i.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap L M : L →* M) a)) :
    Function.Injective (groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) i 2).hom ∧
    ∀ y : groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ) 2,
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ))) 2).hom y = 0 →
      ∃ β : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) 2,
        (groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) i 2).hom β = y := by
  let UM := Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ
  let UL := Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ

  obtain ⟨e, he⟩ := IsGalois.exists_units_quotientToInvariants_iso_res_apply_eq E L M hactL hactM S ι hι

  have hvan : ∀ n : ℕ, 1 ≤ n → n < 2 → Limits.IsZero (groupCohomology (Rep.res S.subtype UM) n) := by
    intro n h1 h2
    obtain rfl : n = 1 := by omega
    exact groupCohomology.isZero_H1_res_units_of_smul_eq E M hactM S
  obtain ⟨hinj, hex⟩ := groupCohomology.inf_injective_and_exact_of_isZero_res UM S 2 hvan

  obtain ⟨ψ, hψ⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv ι (UM.quotientToInvariants S) UL e 2

  have hi' : i = (Rep.resFunctor (QuotientGroup.mk' S)).map e.inv ≫ Rep.ofHom (UM.ρ.quotientToInvariants_lift S) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    exact (hi (Additive.toMul a)).trans (he (Additive.toMul a)).symm
  have hfac : groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) i 2 =
      groupCohomology.map ι.toMonoidHom e.inv 2 ≫
        groupCohomology.map (A := UM.quotientToInvariants S) (B := UM)
          (QuotientGroup.mk' S) (Rep.ofHom (UM.ρ.quotientToInvariants_lift S)) 2 := by
    rw [hi', groupCohomology.map_comp]
    rfl
  have hT : ∀ x, (groupCohomology.map ι.toMonoidHom e.inv 2).hom x = ψ.symm x := fun x => (hψ x).symm
  refine ⟨?_, ?_⟩
  · rw [hfac, ModuleCat.hom_comp]
    refine hinj.comp ?_
    intro a b h
    rw [hT, hT] at h
    exact ψ.symm.injective h
  · intro y hy
    obtain ⟨y', hy'⟩ := hex y hy
    refine ⟨ψ y', ?_⟩
    rw [hfac, ModuleCat.hom_comp, LinearMap.comp_apply, hT, LinearEquiv.symm_apply_apply]
    exact hy'

end M4aHerbrand.UnitsInfRes

theorem solution
    (E L M : Type) [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M]
    [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M]
    [MulDistribMulAction (L ≃ₐ[E] L) Lˣ]
    (hactL : ∀ (g : L ≃ₐ[E] L) (a : Lˣ), ((g • a : Lˣ) : L) = g (a : L))
    [MulDistribMulAction (M ≃ₐ[E] M) Mˣ]
    (hactM : ∀ (g : M ≃ₐ[E] M) (a : Mˣ), ((g • a : Mˣ) : M) = g (a : M))
    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L))
    (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y))
    (i : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ)
    (hi : ∀ a : Lˣ, i.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap L M : L →* M) a)) :
    Function.Injective (groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) i 2).hom ∧
    ∀ y : groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ) 2,
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ))) 2).hom y = 0 →
      ∃ β : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) 2,
        (groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) i 2).hom β = y :=
  M4aHerbrand.UnitsInfRes.main E L M hactL hactM S ι hι i hi

end S_IsGalois_map_two_units_injective_and_exists_of_map_subtype_eq_zero
end P2MW
export P2MW.S_IsGalois_map_two_units_injective_and_exists_of_map_subtype_eq_zero (solution)
