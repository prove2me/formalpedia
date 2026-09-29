-- Prove2me | solution 1 for NumberField.IdeleLocalInv.hasLocalInv_iff_of_forall_map_prG_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8b7e5cf5-3a43-5c7d-91c8-dab10cdb61f2

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_iff_of_forall_map_prG_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (z : (AdeleRing (𝓞 K) K)ˣ), g • z = D.unitsAct g z)
    (x₁ x₂ : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (hx : ∀ (w : HeightOneSpectrum (𝓞 K))
      (prG : Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ),
      (∀ z : (AdeleRing (𝓞 K) K)ˣ, prG.hom (Additive.ofMul z) = Additive.ofMul (finPart w z)) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype prG 2).hom x₁
        = (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype prG 2).hom x₂)
    (v : HeightOneSpectrum (𝓞 E)) (t : AddCircle (1 : ℚ)) :
    NumberField.IdeleLocalInv.HasLocalInv E K D hactI x₁ v t ↔ NumberField.IdeleLocalInv.HasLocalInv E K D hactI x₂ v t := by
  constructor
  · rintro ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', n, hcoord, ht⟩
    exact ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', n, (hx w (prG w) (hpr w)) ▸ hcoord, ht⟩
  · rintro ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', n, hcoord, ht⟩
    exact ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', n, (hx w (prG w) (hpr w)).symm ▸ hcoord, ht⟩

end S_NumberField_IdeleLocalInv_hasLocalInv_iff_of_forall_map_prG_eq
end P2MW
export P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_iff_of_forall_map_prG_eq (solution)
