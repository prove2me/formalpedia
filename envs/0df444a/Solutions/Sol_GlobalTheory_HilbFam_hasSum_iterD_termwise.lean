-- Prove2me | solution 1 for GlobalTheory.HilbFam.hasSum_iterD_termwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:12.031239+00:00
-- url     : https://prove2.me/submissions/95641d8e-588b-4de2-be35-287bd7e9ce25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedComplexPartialDerivativeEqWirtingerWord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedComplexPartialDerivTermwise
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_iteratedFDeriv
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_tsum_of_locally_normal
import Theorems.Thm_GlobalTheory_SCV_hasSum_iteratedFDeriv_of_locally_normal
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply


section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
open Set Filter Topology in
open NumberField IsDedekindDomain in
open scoped ContDiff nonZeroDivisors in
private lemma partialD_eqOn_fderiv_single {I : Type} [Fintype I] [DecidableEq I] {U : Set (I → ℂ)}
    {h : (I → ℂ) → ℂ} (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) (i : I) :
    EqOn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD i h) (fun z ↦ fderiv ℂ h z (Pi.single i 1)) U := by
  intro z hz
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD
  exact (hh.differentiableAt (hU.mem_nhds hz)).lineDeriv_eq_fderiv
open Set Filter Topology in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma iterD_eqOn_iteratedFDeriv_single {I : Type} [Fintype I] [DecidableEq I]
    {U : Set (I → ℂ)} {h : (I → ℂ) → ℂ} (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) :
    ∀ l : List I, EqOn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h)
      (fun z ↦ iteratedFDeriv ℂ l.length h z (fun k ↦ Pi.single (l.get k) 1)) U
  | [] => by
    intro z _
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD]
  | i :: l => by
    intro z hz
    have ih := iterD_eqOn_iteratedFDeriv_single hU hh l
    have hG : DifferentiableOn ℂ
        (fun z ↦ iteratedFDeriv ℂ l.length h z (fun k ↦ Pi.single (l.get k) 1)) U :=
      (_root_.GlobalTheory.SCV.differentiableOn_iteratedFDeriv hU hh l.length).continuousMultilinear_apply_const _
    have hd : DifferentiableOn ℂ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h) U := hG.congr ih
    have hstep : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD (i :: l) h z =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD i (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h) z := by
      simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD]
    have hev : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h =ᶠ[𝓝 z]
        fun z ↦ iteratedFDeriv ℂ l.length h z (fun k ↦ Pi.single (l.get k) 1) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) ih
    rw [hstep, partialD_eqOn_fderiv_single hU hd i hz]
    simp only
    rw [hev.fderiv_eq, fderiv_continuousMultilinear_apply_const_apply
      ((_root_.GlobalTheory.SCV.differentiableOn_iteratedFDeriv hU hh l.length).differentiableAt (hU.mem_nhds hz))]
    exact (iteratedFDeriv_succ_apply_left (f := h) (x := z) (n := l.length)
      (fun k ↦ Pi.single ((i :: l).get k) 1)).symm
end GlobalTheory.HilbFam
end

set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
open Set Filter Topology
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
namespace _root_.GlobalTheory.HilbFam
theorem _root_.solution : ∀ (I : Type) [Fintype I] [DecidableEq I] (Ξ : Type) (u : List I) (r : ℝ)
    (f : Ξ → (I → ℂ) → ℂ) (g : (I → ℂ) → ℂ) (M : Ξ → ℝ), 0 < r → Summable M →
    (∀ ξ, DifferentiableOn ℂ (f ξ) (Metric.ball 0 r)) →
    (∀ ξ, ∀ z ∈ Metric.ball (0 : I → ℂ) r, ‖f ξ z‖ ≤ M ξ) →
    (∀ z ∈ Metric.ball (0 : I → ℂ) r, HasSum (fun ξ ↦ f ξ z) (g z)) →
    HasSum (fun ξ ↦ _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (f ξ) 0) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0) := by
  intro I _ _ Ξ u r f g M hr hM hf hbound hsum
  have hU : IsOpen (Metric.ball (0 : I → ℂ) r) := Metric.isOpen_ball
  have h0 : (0 : I → ℂ) ∈ Metric.ball (0 : I → ℂ) r := Metric.mem_ball_self hr
  have hloc : ∀ x ∈ Metric.ball (0 : I → ℂ) r, ∃ t ∈ 𝓝 x, ∃ v : Ξ → ℝ, Summable v ∧
      ∀ ξ, ∀ z ∈ t, ‖f ξ z‖ ≤ v ξ :=
    fun x hx ↦ ⟨_, hU.mem_nhds hx, M, hM, hbound⟩
  have hg_eq : EqOn g (fun w ↦ ∑' ξ, f ξ w) (Metric.ball 0 r) :=
    fun z hz ↦ (hsum z hz).tsum_eq.symm
  have hg : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (_root_.GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hU hf hloc).congr hg_eq
  have hev : g =ᶠ[𝓝 0] fun w ↦ ∑' ξ, f ξ w := Filter.eventuallyEq_of_mem (hU.mem_nhds h0) hg_eq
  have hS := _root_.GlobalTheory.SCV.hasSum_iteratedFDeriv_of_locally_normal hU hf hloc u.length h0
  rw [← (hev.iteratedFDeriv ℂ u.length).eq_of_nhds] at hS
  rw [iterD_eqOn_iteratedFDeriv_single hU hg u h0]
  simp only [iterD_eqOn_iteratedFDeriv_single hU (hf _) u h0]
  exact ContinuousMultilinearMap.hasSum_eval hS _
end _root_.GlobalTheory.HilbFam
end GlobalTheory.HilbFam
