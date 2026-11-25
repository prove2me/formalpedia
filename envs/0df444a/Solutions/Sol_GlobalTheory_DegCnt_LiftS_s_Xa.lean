-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.s_Xa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:29.78345+00:00
-- url     : https://prove2.me/submissions/7ec47071-dc22-45b9-ad55-6a06e349a063

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_Xa_mono
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnipStab_Xa_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution (G : FlagD H r) {s : V →ₗ[K] V} (hs : G.InN s) (a : ℕ) {y : V} (hy : y ∈ G.Xa a) :
    s y ∈ G.Xa a := by
  obtain ⟨-, -, he, -⟩ := hs
  have key : ∀ b : Fin r, b.val < a → s (G.e b.castSucc) ∈ G.Xa a := by
    intro b hb
    have h1 : s (G.e b.castSucc) - G.e b.castSucc ∈ G.Xa a := Xa_mono G hb.le (he b)
    have h2 : G.e b.castSucc ∈ G.Xa a := Submodule.subset_span ⟨b, hb, rfl⟩
    simpa using add_mem h1 h2
  have hle : G.Xa a ≤ (G.Xa a).comap s := Submodule.span_le.2 (by
    rintro _ ⟨b, hb, rfl⟩
    exact key b hb)
  exact hle hy
end GlobalTheory.DegCnt.LiftS
