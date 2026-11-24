-- Prove2me | solution 1 for GlobalTheory.IntPair.RedMap.ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:26.195087+00:00
-- url     : https://prove2.me/submissions/74b56bd2-087b-4e7e-8d43-899215b583c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinrankLeFinrankInfPerpXPlus
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_SameRedEquivalence
import Theorems.Thm_GlobalTheory_IntPair_RedMap_mk_out
import Theorems.Thm_GlobalTheory_IntPair_RedMap_mk_eq_mk

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
theorem _root_.solution {b c : RedMap F F' F'' Λ g} (h : SameRed F' F'' b.out c.out) : b = c := by
  rw [← b.mk_out, ← c.mk_out]; exact (mk_eq_mk _ _).2 h
end GlobalTheory.IntPair.RedMap
