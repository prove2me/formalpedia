-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.symm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:34:58.519129+00:00
-- url     : https://prove2.me/submissions/5a9015e1-fdc3-495c-a339-1ef7a459e287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
omit [NumberField K] [StarRing K] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution (s : V ≃ₗ[K] V) (n : ℕ) (hn : ((s : V →ₗ[K] V) - 1) ^ n = 0) (Q : Submodule (𝓞 K) V)
    (h : ∀ x ∈ Q, s x - x ∈ Q) {y : V} (hy : y ∈ Q) : s.symm y ∈ Q := by
  set M : V →ₗ[K] V := (s : V →ₗ[K] V) - 1 with hM
  have hneg : ∀ x ∈ Q, (-M) x ∈ Q := by
    intro x hx
    have := Q.neg_mem (h x hx)
    simpa [hM] using this
  have hpow : ∀ k : ℕ, ∀ x ∈ Q, ((-M) ^ k) x ∈ Q := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; rw [pow_succ', Module.End.mul_apply]; exact hneg _ (ih x hx)
  have hg : (s : V →ₗ[K] V) * ∑ i ∈ Finset.range n, (-M) ^ i = 1 := by
    have := mul_neg_geom_sum (-M) n
    rw [neg_pow, hn, mul_zero, sub_zero, sub_neg_eq_add, hM, add_sub_cancel] at this
    exact this
  have e : s.symm y = (∑ i ∈ Finset.range n, (-M) ^ i) y := by
    apply s.injective
    rw [LinearEquiv.apply_symm_apply]
    have := congrArg (fun f : V →ₗ[K] V => f y) hg
    simpa [Module.End.mul_apply] using this.symm
  rw [e, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ => hpow i y hy
end GlobalTheory.DegCnt.LiftS
