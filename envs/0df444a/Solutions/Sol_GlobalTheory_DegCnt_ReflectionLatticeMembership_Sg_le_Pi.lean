-- Prove2me | solution 1 for GlobalTheory.DegCnt.ReflectionLatticeMembership.Sg_le_Pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:20.195158+00:00
-- url     : https://prove2.me/submissions/8564de11-c5e6-426d-8a67-dc95dea78cad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ReferenceLatticeMemOfMemInnerSpan
import Theorems.Thm_GlobalTheory_DegCnt_NFGeom_Pi_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open Formalism.HermitianLatticeCounting.P
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.ReflectionLatticeMembership
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
namespace GlobalTheory.DegCnt.ReflectionLatticeMembership
theorem _root_.solution [FiniteDimensional K V] : Sg N ≤ N.Pi := by
  rw [NFGeom.Pi_eq]
  exact sup_le (sup_le (le_sup_of_le_left (le_sup_left.trans le_sup_left))
    (le_sup_of_le_left (le_sup_right.trans le_sup_left))) le_sup_right
end GlobalTheory.DegCnt.ReflectionLatticeMembership
