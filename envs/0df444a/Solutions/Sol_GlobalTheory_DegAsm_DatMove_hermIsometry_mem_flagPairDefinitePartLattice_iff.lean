-- Prove2me | solution 1 for GlobalTheory.DegAsm.DatMove.hermIsometry_mem_flagPairDefinitePartLattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:57.732476+00:00
-- url     : https://prove2.me/submissions/89a3adcc-e362-4662-9382-4f631c6f06e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotent
import Theorems.Thm_GlobalTheory_DegAsm_DatMove_sup_iff
import Theorems.Thm_GlobalTheory_DegAsm_DatMove_push_X
import Theorems.Thm_GlobalTheory_DegAsm_DatMove_hermFrameMapIsometry_frameSpan
import Theorems.Thm_GlobalTheory_DegAsm_DatMove_perp_map_iff
import Theorems.Thm_GlobalTheory_DegAsm_DatMove_push_X_iff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.DatMove
open AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y)
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
namespace GlobalTheory.DegAsm.DatMove
theorem _root_.solution (F G : FlagD H r) {Λ Λ' : Submodule R V} (h : ∀ y, s y ∈ Λ' ↔ y ∈ Λ) (y : V) :
    s y ∈ flagPairDefinitePartLattice (push s hs F) (push s hs G) Λ' ↔ y ∈ flagPairDefinitePartLattice F G Λ := by
  have h1 := sup_iff s.toAddEquiv (A' := rs R (push s hs F).X) (B' := rs R F.X) h (push_X_iff s hs F) y
  simp only [flagPairDefinitePartLattice, latL, uPerp, wSp, Submodule.mem_inf, Submodule.restrictScalars_mem]
  rw [hermFrameMapIsometry_frameSpan, perp_map_iff s hs]
  refine and_congr (and_congr ?_ h1) Iff.rfl
  rw [push_X, push_X, ← Submodule.map_sup, perp_map_iff s hs]
end GlobalTheory.DegAsm.DatMove
