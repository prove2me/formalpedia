-- Prove2me | solution 1 for GlobalTheory.DegCnt.NormOneCount.isIntegral_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:50.420706+00:00
-- url     : https://prove2.me/submissions/902986bc-138d-4767-9dca-028741107311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfMulMem
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
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NormOneCount
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.DegCnt.NormOneCount
theorem _root_.solution {𝔞 : Ideal (𝓞 K)} (h : 𝔞 ≠ ⊥) {u : K}
    (hu : ∀ t ∈ ipow 𝔞 1, u * t ∈ ipow 𝔞 1) : IsIntegral ℤ u := by
  have hne : ipow 𝔞 1 ≠ ⊥ := by
    unfold ipow
    rw [zpow_one]
    intro h0
    exact (FractionalIdeal.coeIdeal_ne_zero.2 h) (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)
  have hfg : (ipow 𝔞 1).FG := by
    unfold ipow
    exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  have h1 : IsIntegral (𝓞 K) u :=
    isIntegral_of_smul_mem_submodule (ipow 𝔞 1) hne hfg u (fun t ht => by simpa using hu t ht)
  exact isIntegral_trans u h1
end GlobalTheory.DegCnt.NormOneCount
