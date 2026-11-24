-- Prove2me | solution 1 for GlobalTheory.PrimeSection.compatible_of_res_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:06:01.795913+00:00
-- url     : https://prove2.me/submissions/8bfec1f5-b4c6-4059-9bdd-b4a468518fc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_germ_res
import Theorems.Thm_GlobalTheory_PrimeSection_eq_of_germ_eq
import Theorems.Thm_GlobalTheory_PrimeSection_germ_eq_mul_germ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
variable [IsIntegral X]
variable {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
namespace GlobalTheory.PrimeSection
theorem _root_.solution {D : X.Opens} (hD : genericPoint X ∈ D) {r : ∀ a, Γ(X, U a ⊓ D)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ D ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_right)).op (r b))
    (c : Γ(X, D)) {s : ∀ a, Γ(X, U a)}
    (hs : ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      X.presheaf.map (homOfLE inf_le_right).op c * r a) (a b : ι) :
    X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b) := by
  refine eq_of_germ_eq fun hab => ?_
  have hga : genericPoint X ∈ U a ⊓ D := ⟨hab.1, hD⟩
  have hgb : genericPoint X ∈ U b ⊓ D := ⟨hab.2, hD⟩
  rw [map_mul, germ_res, germ_res]
  rw [← germ_res (inf_le_left : U a ⊓ D ≤ U a) hga (s a), hs a,
    ← germ_res (inf_le_left : U b ⊓ D ≤ U b) hgb (s b), hs b]
  rw [map_mul, map_mul, germ_res, germ_res, germ_eq_mul_germ hr hga hgb]
  ring
end GlobalTheory.PrimeSection
