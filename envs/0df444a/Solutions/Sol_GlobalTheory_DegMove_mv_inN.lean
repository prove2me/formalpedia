-- Prove2me | solution 1 for GlobalTheory.DegMove.mv_inN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:30:30.681202+00:00
-- url     : https://prove2.me/submissions/b1a61cb6-f790-4e0b-b476-d2b43a9e4a09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_isomGrp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.DegMove
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ} {s : V ≃ₗ[K] V}
variable (hs : s ∈ isomGrp H) (F F' : FlagD H r)
namespace GlobalTheory.DegMove
theorem _root_.solution (n : V ≃ₗ[K] V) :
    (mv hs F).InN ((MulAut.conj s n : V ≃ₗ[K] V) : V →ₗ[K] V) ↔ F.InN (n : V →ₗ[K] V) := by
  have e : ∀ x, ((MulAut.conj s n : V ≃ₗ[K] V) : V →ₗ[K] V) (s x) = s ((n : V →ₗ[K] V) x) := fun x => by
    simp
  unfold FlagD.InN
  refine and_congr ?_ (and_congr (iff_of_true (LinearEquiv.bijective _) (LinearEquiv.bijective _))
    (and_congr ?_ ?_))
  · rw [s.surjective.forall₂]
    simp only [e, (mem_isomGrp H s).1 hs]
  · simp only [mv_e, e, mv_Xa, ← map_sub, memK]
  · rw [s.surjective.forall]
    simp only [mv_e, e, mv_X, ← map_sub, memK, (mem_isomGrp H s).1 hs]
end GlobalTheory.DegMove
