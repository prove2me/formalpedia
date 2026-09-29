-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.bcMap_genericPoint_specializes_crossingPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4e007061-a0f0-5cbb-bf0c-3527398417bf

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_bcMap_genericPoint_specializes_crossingPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] (ρO : R p →+* O)
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n ∧ 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n := by
  haveI := (𝔛.Mfib A hA ρ hρ).isIntegral

  set z0 := (inv (𝔛.efib A hA ρ hρ)).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) with hz0
  set z1 := (inv (𝔛.efib A hA ρ hρ)).base ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) with hz1
  have he0 : (𝔛.efib A hA ρ hρ).base z0 = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n := by
    rw [hz0, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have he1 : (𝔛.efib A hA ρ hρ).base z1 = (pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n := by
    rw [hz1, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have h0 : 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n = (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base z0 := by
    rw [Scheme.Hom.comp_apply, he0]; rfl
  have h1 : 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n = (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base z1 := by
    rw [Scheme.Hom.comp_apply, he1, ← Scheme.Hom.comp_apply, ← pullback.condition_assoc]
  constructor
  · rw [h0]
    exact (genericPoint_specializes z0).map (Scheme.Hom.continuous _)
  · rw [h1]
    exact (genericPoint_specializes z1).map (Scheme.Hom.continuous _)

end S_ModularCurve_XHDRModelAtP_bcMap_genericPoint_specializes_crossingPt
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_bcMap_genericPoint_specializes_crossingPt (solution)
