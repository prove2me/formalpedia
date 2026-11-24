-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.over_bar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:57.873838+00:00
-- url     : https://prove2.me/submissions/ee271023-7d17-4cd3-9e88-cccdbf379de6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
local notation "cc" => IsCMField.complexConj E
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {w : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (OF E)} (h : Over w v) : Over (bar w) v := by
  unfold Over at h ⊢
  rw [← h]
  ext y
  have : RingOfIntegers.mapRingEquiv (cc).toRingEquiv (algebraMap (OF E) (𝓞 E) y) = algebraMap (OF E) (𝓞 E) y :=
    RingOfIntegers.ext ((cc).commutes (y : maximalRealSubfield E))
  change RingOfIntegers.mapRingEquiv (cc).toRingEquiv (algebraMap (OF E) (𝓞 E) y) ∈ w.asIdeal ↔
    algebraMap (OF E) (𝓞 E) y ∈ w.asIdeal
  rw [this]
end GlobalTheory.CMVal.ValEx
