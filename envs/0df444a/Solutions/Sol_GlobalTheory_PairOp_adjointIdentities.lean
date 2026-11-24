-- Prove2me | solution 1 for GlobalTheory.PairOp.adjointIdentities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:55:10.617222+00:00
-- url     : https://prove2.me/submissions/26338d8d-0e48-4e04-86d1-e02b890febcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_FF_dia
import Theorems.Thm_GlobalTheory_PairOp_FFStar_dia
import Theorems.Thm_GlobalTheory_PairOp_dia_dia
import Theorems.Thm_GlobalTheory_PairOp_mem_ram
import Theorems.Thm_GlobalTheory_PairOp_resCard_ne_zero
import Theorems.Thm_GlobalTheory_PairOp_FFStar_FF_ram
import Theorems.Thm_GlobalTheory_PairOp_FF_FFStar_ram
import Theorems.Thm_GlobalTheory_PairOp_unit_FFStar_FF
import Theorems.Thm_GlobalTheory_PairOp_unit_FF_FFStar
import Theorems.Thm_GlobalTheory_PairOp_keepsFinite_sumOp
import Theorems.Thm_GlobalTheory_PairOp_keepsFinite_dia
import Theorems.Thm_GlobalTheory_PairOp_keepsFinite_mul
import Theorems.Thm_GlobalTheory_PairOp_isAdj_mul
import Theorems.Thm_GlobalTheory_PairOp_isAdj_sum
import Theorems.Thm_GlobalTheory_PairOp_isAdj_dia
import Theorems.Thm_GlobalTheory_PairOp_isScaledUnitaryOn
import Theorems.Thm_GlobalTheory_PairOp_dia_unitary
import Theorems.Thm_GlobalTheory_LatPair_Model_FF_dia
import Theorems.Thm_GlobalTheory_LatPair_Model_isAdj_sumOp
import Theorems.Thm_GlobalTheory_LatPair_conj_resChar
import Theorems.Thm_GlobalTheory_LatPair_resChar_ne_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}
namespace GlobalTheory.PairOp
theorem _root_.solution [Fintype n] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) :
    AdjointIdentities k n q (resChar ψ hψ q) := by
  classical
  have hχ : resChar ψ hψ q ≠ 1 := resChar_ne_one hψ q
  have hFF : KeepsFinite (n := n) (FF q (resChar ψ hψ q)) := by
    unfold FF
    exact keepsFinite_sumOp _ (fun Q => withKer Q.lat) _ fun P Q hQ =>
      mem_withKer.mpr (mem_withLat.mp hQ).symm
  have hFFS : KeepsFinite (n := n) (FFStar q (resChar ψ hψ q)) := by
    unfold FFStar
    exact keepsFinite_sumOp _ (fun Q => withLat Q.ker) _ fun P Q hQ =>
      mem_withLat.mpr (mem_withKer.mp hQ).symm
  have hD : KeepsFinite (n := n) (D q) := by
    unfold D Da
    exact keepsFinite_sumOp _ (fun Q => withKer Q.lat) _ fun P Q hQ =>
      mem_withKer.mpr (mem_withLat.mp (Finset.mem_filter.mp hQ).1).symm
  have hU : KeepsFinite (n := n) (U q) := by
    unfold U
    exact keepsFinite_sumOp _ (fun Q => withLat Q.ker) _ fun P Q hQ =>
      mem_withLat.mpr (mem_withKer.mp (Finset.mem_filter.mp hQ).1).symm
  have hadj : IsAdj (n := n) (FF q (resChar ψ hψ q)) (FFStar q (resChar ψ hψ q)) := by
    unfold FF FFStar
    refine Model.isAdj_sumOp _ _ _ _ (fun P Q => ?_) fun P Q _ => ?_
    · simp only [mem_withLat, mem_withKer]
      exact eq_comm
    · rw [conj_resChar, neg_neg]
  have hq : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ resCard_ne_zero
  have hqr : (starRingEnd ℂ) ((resCard k : ℂ) ^ Fintype.card n) = (resCard k : ℂ) ^ Fintype.card n := by simp
  have hram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n ℂ, dia c φ ∈ Mram k n ℂ := fun c φ h =>
    mem_ram (fun d => dia_dia c d) h
  have hunit : ∀ c : 𝓀[k]ˣ, IsAdj (n := n) (dia c⁻¹ * FF q (resChar ψ hψ q)) (dia c * FFStar q (resChar ψ hψ q)) ∧
      IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia c⁻¹ * FF q (resChar ψ hψ q)) := by
    intro c
    have hA : IsAdj (n := n) (dia c⁻¹ * FF q (resChar ψ hψ q)) (dia c * FFStar q (resChar ψ hψ q)) := by
      have e := isAdj_mul (isAdj_dia c⁻¹) hadj hFF (keepsFinite_dia _)
      rwa [inv_inv, FFStar_dia] at e
    refine ⟨hA, isScaledUnitaryOn hq hqr (keepsFinite_mul (keepsFinite_dia _) hFF)
      (keepsFinite_mul (keepsFinite_dia _) hFFS) (fun φ h => ?_) (fun φ h => ?_) hA (fun φ h => ?_) fun φ h => ?_⟩
    · rw [Module.End.mul_apply]
      exact hram _ _ (mem_ram (fun d => FF_dia q _ d) h)
    · rw [Module.End.mul_apply]
      exact hram _ _ (mem_ram (fun d => FFStar_dia q _ d) h)
    · have e := LinearMap.congr_fun (unit_FFStar_FF q (resChar ψ hψ q) c) φ
      simp only [Module.End.mul_apply] at e ⊢
      rw [e, FFStar_FF_ram q hχ h]
    · have e := LinearMap.congr_fun (unit_FF_FFStar q (resChar ψ hψ q) c) φ
      simp only [Module.End.mul_apply] at e ⊢
      rw [e, FF_FFStar_ram q hχ h]
  have hm : ((-1 : 𝓀[k]ˣ))⁻¹ = -1 := by simp
  refine ⟨⟨hFF, hFFS⟩, ⟨hD, hU⟩, hadj, ?_, ?_, ?_, fun c => isAdj_dia c,
    fun c => ⟨dia_unitary (fun _ _ _ => Submodule.mem_top) c, dia_unitary hram c⟩, ?_, ?_, hunit⟩
  · exact isScaledUnitaryOn hq hqr hFF hFFS (fun φ h => mem_ram (fun d => FF_dia q _ d) h)
      (fun φ h => mem_ram (fun d => FFStar_dia q _ d) h) hadj (fun φ h => FFStar_FF_ram q hχ h)
      fun φ h => FF_FFStar_ram q hχ h
  · unfold Gs GsStar
    exact isAdj_sum _ _ _ _ _ (fun c => by rw [conj_resChar, neg_neg]) fun c => isAdj_dia c
  · unfold U D Da
    refine Model.isAdj_sumOp _ _ _ _ (fun P Q => ?_) fun _ _ _ => by simp
    simp only [Finset.mem_filter, mem_withKer, mem_withLat]
    exact and_congr eq_comm Iff.rfl
  · have e := (hunit (-1)).1
    rwa [hm] at e
  · have e := (hunit (-1)).2
    rwa [hm] at e
end GlobalTheory.PairOp
