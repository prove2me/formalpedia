-- Prove2me | solution 1 for GlobalTheory.DegCnt.FlagDisc.idx_ipow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:26:11.773797+00:00
-- url     : https://prove2.me/submissions/a40926da-5ca2-40a2-921f-1fd3851837ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinor
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_mem_ipow_iff
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_mem_ipow_nat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_absNorm_mul_relIndex_one
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FlagDisc
open GlobalTheory.DegCnt.DelScale GlobalTheory.DegCnt.Absorb
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [StarRing K]
namespace GlobalTheory.DegCnt.FlagDisc
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) (hn : 0 ≤ n) :
    (1 : K) ∈ ipow 𝔡 (-n) ∧ (idx (ipow 𝔡 (-n)) 1 : ℝ) = (Ideal.absNorm 𝔡 : ℝ) ^ n := by
  lift n to ℕ using hn
  have h1 : (1 : K) ∈ ipow 𝔡 (-n) := by
    rw [mem_ipow_iff h, neg_neg]
    intro u hu
    obtain ⟨d, -, rfl⟩ := (mem_ipow_nat 𝔡 n u).1 hu
    exact Submodule.mem_one.2 ⟨d, (one_mul _).symm⟩
  refine ⟨h1, ?_⟩
  have hfg : (ipow 𝔡 (-n)).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  have := ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.absNorm_mul_relIndex_one (ipow 𝔡 (-n)) hfg (Submodule.one_le.2 h1)
  have e : (⟨ipow 𝔡 (-n), FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (𝓞 K)⁰ K) =
      (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n : ℤ)) := rfl
  rw [e, map_zpow₀, FractionalIdeal.coeIdeal_absNorm, zpow_neg, inv_mul_eq_one₀ (zpow_ne_zero _
    (by exact_mod_cast fun e => h (Ideal.absNorm_eq_zero_iff.1 e)))] at this
  have := congrArg (fun q : ℚ => (q : ℝ)) this
  simpa [idx] using this.symm
end GlobalTheory.DegCnt.FlagDisc
