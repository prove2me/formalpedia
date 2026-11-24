-- Prove2me | solution 1 for GlobalTheory.PrimeSection.mem_basicOpen_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:55.23241+00:00
-- url     : https://prove2.me/submissions/b6ed14f8-5bd1-41cf-8543-10916ccd37e7

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
omit [IsIntegral X]
namespace GlobalTheory.PrimeSection
theorem _root_.solution (hg : ∀ a b, IsUnit (g a b)) {s : ∀ a, Γ(X, U a)}
    (hs : ∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b))
    {a b : ι} {x : X} (ha : x ∈ U a) (hb : x ∈ X.basicOpen (s b)) : x ∈ X.basicOpen (s a) := by
  have hxb : x ∈ U b := X.basicOpen_le (s b) hb
  have hab : x ∈ U a ⊓ U b := ⟨ha, hxb⟩
  have h := congrArg (X.presheaf.germ _ x hab) (hs a b)
  rw [map_mul, germ_res, germ_res] at h
  rw [X.mem_basicOpen (s a) x ha, h]
  exact (IsUnit.mul (IsUnit.map (X.presheaf.germ _ x hab).hom (hg a b)) ((X.mem_basicOpen (s b) x hxb).mp hb))
end GlobalTheory.PrimeSection
