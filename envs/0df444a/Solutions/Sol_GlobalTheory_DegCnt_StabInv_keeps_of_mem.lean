-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.keeps_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:34.619299+00:00
-- url     : https://prove2.me/submissions/bec35320-fc2e-4031-9cb8-f5f4db4a141b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_keeps_one
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_Keeps_mul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_Keeps_inv
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_keeps_of_inN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.StabInv
theorem _root_.solution [FiniteDimensional K V] (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.R) :
    Keeps N.F s ∧ Keeps N.F' s := by
  unfold NF.R at hs
  induction hs using Subgroup.closure_induction with
  | mem x hx => exact ⟨keeps_of_inN hx.1, keeps_of_inN hx.2⟩
  | one => exact ⟨keeps_one _, keeps_one _⟩
  | mul x y _ _ hx hy => exact ⟨hx.1.mul hy.1, hx.2.mul hy.2⟩
  | inv x _ hx => exact ⟨hx.1.inv, hx.2.inv⟩
end GlobalTheory.DegCnt.StabInv
