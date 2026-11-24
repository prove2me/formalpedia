-- Prove2me | solution 1 for GlobalTheory.IntPair.RedMap.mk_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:31.672847+00:00
-- url     : https://prove2.me/submissions/58cbb9e0-8d20-4d35-9ef1-554c38b2f377

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinrankLeFinrankInfPerpXPlus
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_SameRedEquivalence
import Theorems.Thm_GlobalTheory_IntPair_sameRed_equivalence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntPair
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Module
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
variable {F F' F'' F₁ G' G'' : FlagD H r} {Λ Λ₁ : Submodule R V} {g : R} {β β₁ s s₁ s₂ : V ≃ₗ[K] V}
open GlobalTheory.IntPair.RedMap
namespace GlobalTheory.IntPair.RedMap
theorem _root_.solution (h : IsPairMap F F' F'' Λ g β) (h₁ : IsPairMap F F' F'' Λ g β₁) :
    mk β h = mk β₁ h₁ ↔ SameRed F' F'' β β₁ :=
  ⟨fun e => ((sameRed_equivalence F' F'').comap Subtype.val).eqvGen_iff.1 (Quot.eq.1 e), fun e => Quot.sound e⟩
end GlobalTheory.IntPair.RedMap
