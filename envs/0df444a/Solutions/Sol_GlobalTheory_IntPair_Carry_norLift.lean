-- Prove2me | solution 1 for GlobalTheory.IntPair.Carry.norLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:46.164801+00:00
-- url     : https://prove2.me/submissions/7bbed398-ab3c-4107-b6ed-fe44f378ac92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinrankLeFinrankInfPerpXPlus
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_SameRedEquivalence
import Theorems.Thm_GlobalTheory_IntPair_Carry_perp_iff
import Theorems.Thm_GlobalTheory_IntPair_Carry_V0
import Theorems.Thm_GlobalTheory_IntPair_Carry_xPlus

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
variable [FiniteDimensional K V]
omit [FiniteDimensional K V]
open GlobalTheory.IntPair.Carry
namespace GlobalTheory.IntPair.Carry
theorem _root_.solution (h : Carry s F F₁) (k : Carry s F' G') (x : V) : s x ∈ norLift F₁ G' ↔ x ∈ norLift F F' :=
  and_congr (h.V0 k x) (h.perp_iff h.xPlus x)
end GlobalTheory.IntPair.Carry
