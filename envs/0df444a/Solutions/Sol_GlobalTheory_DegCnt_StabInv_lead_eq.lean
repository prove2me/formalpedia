-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.lead_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:47.798141+00:00
-- url     : https://prove2.me/submissions/d7da254d-56c9-4d19-b58c-a74f8524bd0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_Keeps_inv
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_lead_le
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.StabInv
theorem _root_.solution {F : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (Λ : Submodule (𝓞 K) V)
    (a : Fin (r + 1)) : lead F (s • Λ) a = lead F Λ a := by
  refine le_antisymm ?_ (lead_le h Λ a)
  simpa using lead_le h.inv (s • Λ) a
end GlobalTheory.DegCnt.StabInv
