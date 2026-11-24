-- Prove2me | solution 1 for GlobalTheory.PrimeSection.germ_eq_mul_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:46:35.699342+00:00
-- url     : https://prove2.me/submissions/b3e21526-164d-4871-aa17-64c695198fcb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_germ_res

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
theorem _root_.solution {D : X.Opens} {r : ∀ a, Γ(X, U a ⊓ D)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ D ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_right)).op (r b))
    {a b : ι} {x : X} (ha : x ∈ U a ⊓ D) (hb : x ∈ U b ⊓ D) :
    X.presheaf.germ _ x ha (r a) =
      X.presheaf.germ _ x (show x ∈ U a ⊓ U b from ⟨ha.1, hb.1⟩) (g a b) *
        X.presheaf.germ _ x hb (r b) := by
  have hx : x ∈ U a ⊓ U b ⊓ D := ⟨⟨ha.1, hb.1⟩, ha.2⟩
  have h := congrArg (X.presheaf.germ _ x hx) (hr a b)
  rw [map_mul, germ_res, germ_res, germ_res] at h
  exact h
end GlobalTheory.PrimeSection
