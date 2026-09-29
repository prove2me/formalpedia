-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.crossingPt_mem_preimage_iotaFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3458259f-c240-5556-ad96-a9a317346b06

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_eq_spec_map_comp_iotaFin_of_comp_base_eq
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_crossingPt_mem_preimage_iotaFin

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1))) :
    𝔛.crossingPt ρO toκ n ∈
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) := by
  classical
  obtain ⟨⟨hcl, -⟩, -⟩ := 𝔛.node_pin κ (toκ.comp ρO) n
  obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton κ
    (𝔛.Mfib κ (toκ.comp ρO)).toBase _ (mem_closedPoints_iff.mp hcl)
  have hinv : (𝔛.efib κ (toκ.comp ρO)).base ((inv (𝔛.efib κ (toκ.comp ρO))).base
      ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)) =
      (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have huκ : (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0).base n =
      (z.left ≫ 𝔛.efib κ (toκ.comp ρO) ≫ 𝔛.comp κ (toκ.comp ρO) 0).base (IsLocalRing.closedPoint κ) := by
    simp only [Scheme.Hom.comp_apply]
    rw [← hinv, ← hz]
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨ψ, hψ⟩ := ModularCurve.DRModelPackageLevel.exists_eq_spec_map_comp_iotaFin_of_comp_base_eq N₀ q hqN 𝔛 κ
    (toκ.comp ρO) (RingHom.id κ)
    (fun c hc => by
      by_contra h
      exact ((IsLocalRing.mem_maximalIdeal c).mp hc) (isUnit_iff_ne_zero.mpr h))
    ((z.left ≫ 𝔛.efib κ (toκ.comp ρO) ≫ 𝔛.comp κ (toκ.comp ρO) 0) ≫
      pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))))
    (z.left ≫ 𝔛.efib κ (toκ.comp ρO) ≫ 𝔛.comp κ (toκ.comp ρO) 0)
    (by rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]) n huκ

  have h1 : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))).base
      ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0).base n) ∈
      (IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤ := by
    have e1 : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))).base
        ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0).base n) =
        (IgusaScheme.ιFin (N₀ * q) q).base ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint κ)) := by
      rw [huκ]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun g => g.base (IsLocalRing.closedPoint κ)) hψ).trans (Scheme.Hom.comp_apply _ _ _))
    rw [e1]
    exact ⟨_, trivial, rfl⟩

  have hbc : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) := by
    simp only [DRLevel.bcMap, pullback.map, pullback.lift_fst, Category.comp_id]
  show (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base _ ∈ (IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤
  rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hbc]
  simp only [Scheme.Hom.comp_apply] at h1 ⊢
  exact h1

end S_ModularCurve_DRModelPackageLevel_crossingPt_mem_preimage_iotaFin
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_crossingPt_mem_preimage_iotaFin (solution)
