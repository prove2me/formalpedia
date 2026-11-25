-- Prove2me | solution 1 for GlobalTheory.DegCnt.Absorb.mem_ipow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:29:36.585882+00:00
-- url     : https://prove2.me/submissions/1a13951a-fe30-460c-a3fc-5a412663b60e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Absorb
variable {K : Type} [Field K] [NumberField K]
open NumberField
open scoped Pointwise ENNReal Classical nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.DegCnt.Absorb
namespace _root_.GlobalTheory.DegCnt.Absorb
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) (x : K) :
    x ∈ _root_.GlobalTheory.DegCnt.ipow 𝔡 n ↔ ∀ u ∈ _root_.GlobalTheory.DegCnt.ipow 𝔡 (-n),
      x * u ∈ (1 : Submodule (𝓞 K) K) := by
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-n) ≠ 0 :=
    zpow_ne_zero _ (by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero])
  rw [_root_.GlobalTheory.DegCnt.ipow, _root_.GlobalTheory.DegCnt.ipow, FractionalIdeal.mem_coe,
    ← inv_inv ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n), ← zpow_neg, FractionalIdeal.mem_inv_iff h0]
  refine forall₂_congr fun u _ => ?_
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]
end _root_.GlobalTheory.DegCnt.Absorb
end GlobalTheory.DegCnt.Absorb
