-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.exists_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:27:41.407625+00:00
-- url     : https://prove2.me/submissions/c555a137-de42-49b5-a891-a6e63b8ec116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Theorems.Thm_GlobalTheory_AffineQuotient_toQuot_fromQuot
import Theorems.Thm_GlobalTheory_AffineQuotient_of_charts
import Theorems.Thm_GlobalTheory_AffineQuotient_isPullback_of_charts
import Theorems.Thm_GlobalTheory_AffineQuotient_SpecMap_pullOver
import Theorems.Thm_GlobalTheory_AffineQuotient_isPullback_pullOver
import Theorems.Thm_GlobalTheory_AffineQuotient_fromSpec_toQuot
import Theorems.Thm_GlobalTheory_AffineQuotient_isPullback_toQuot
import Theorems.Thm_GlobalTheory_AffineQuotient_exists_fromSpec_eq
import Theorems.Thm_GlobalTheory_AffineQuotient_isFinite_fromQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc (attr := simp)] GlobalTheory.AffineQuotient.toQuot_fromQuot

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency false
omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
namespace GlobalTheory.AffineQuotient
theorem _root_.solution [IsFinite f] [IsAffineHom g] [IsLocallyNoetherian Y]
    (H : ∀ U : Y.affineOpens, (invariants f g a ha p hp U.1).subtype.FaithfullyFlat ∧
      IsPushout (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype)
        (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype)
        (pullOver f g a ha U.1) (pullOver f g p hp U.1)) :
    ∃ (Q : Scheme.{0}) (q : X ⟶ Q) (π : Q ⟶ Y), q ≫ π = f ∧ IsFinite π ∧ IsFinite q ∧ Flat q ∧
      Surjective q ∧ IsPullback a p q q := by
  have h1 := isFinite_fromQuot f g a ha p hp
  have hc : ∀ y, ∃ (U : Y.affineOpens) (z : _), (cover f g a ha p hp).f U z = y :=
    fun y ↦ (cover f g a ha p hp).exists_eq y
  refine ⟨_, toQuot f g a ha p hp, fromQuot f g a ha p hp, toQuot_fromQuot .., h1, ?_, ?_, ?_, ?_⟩
  · have : IsFinite (toQuot f g a ha p hp ≫ fromQuot f g a ha p hp) := by
      rw [toQuot_fromQuot]; infer_instance
    exact .of_comp _ (fromQuot f g a ha p hp)
  · exact of_charts _ @Flat _ _ _ _ _ hc
      (fun U ↦ isPullback_toQuot f g a ha p hp U (U.2.preimage f))
      fun U ↦ ((flat_and_surjective_SpecMap_iff _).2 (H U).1).1
  · exact of_charts _ @Surjective _ _ _ _ _ hc
      (fun U ↦ isPullback_toQuot f g a ha p hp U (U.2.preimage f))
      fun U ↦ ((flat_and_surjective_SpecMap_iff _).2 (H U).1).2
  · refine isPullback_of_charts a p _ _ _ _ _ _ _ (exists_fromSpec_eq f)
      (fun U ↦ isPullback_pullOver f g a ha (U.2.preimage f) (U.2.preimage g)) fun U ↦ ?_
    rw [← SpecMap_pullOver f g p hp (U.2.preimage f), fromSpec_toQuot]
    exact (isPullback_SpecMap_of_isPushout _ _ _ _ (H U).2).paste_vert
      (isPullback_toQuot f g a ha p hp U (U.2.preimage f))
end GlobalTheory.AffineQuotient
