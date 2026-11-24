-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.TestNearE.exists_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:09:36.188407+00:00
-- url     : https://prove2.me/submissions/074a7cb1-3e7f-4ecc-a8f8-fbfbe1156663

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity
import Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_continuous_topRows
import Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_topRows_eMat_mul
import Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_topRows_eMat
import Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_isOpen_vle
import Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_isCompact_vle_sub
import Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_exists_nhds_one
import Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_nhds_zero_basis
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open GlobalTheory GlobalTheory.GodementJacquet GlobalTheory.GodementJacquet.TestNearE
open ValuativeRel Filter Topology
namespace GlobalTheory.GodementJacquet.TestNearE
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (S : Set (GL (Fin r) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin r) k) ∈ S) :
    ∃ Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ, Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) ∧
      Φ (eMat k r t) = 1 ∧ (∀ x, Φ x = 0 ∨ Φ x = 1) ∧
      ∀ g : GL (Fin r) k, Φ (eMat k r t * g.val) ≠ 0 → g ∈ S := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  set e := eMat k r t
  obtain ⟨W, hW, hWS⟩ := exists_nhds_one r S hS h1
  have hP : topRows r t ⁻¹' W ∈ 𝓝 e :=
    (continuous_topRows (k := k) r t).continuousAt.preimage_mem_nhds (by rw [topRows_eMat]; exact hW)
  have hP' : (fun y => y + e) ⁻¹' (topRows r t ⁻¹' W) ∈ 𝓝 (0 : Matrix (Fin (r + t)) (Fin r) k) :=
    (continuous_add_right e).continuousAt.preimage_mem_nhds (by rw [zero_add]; exact hP)
  obtain ⟨⟨I, J, γ⟩, -, hsub⟩ := (nhds_zero_basis k (r + t) r).mem_iff.mp hP'
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  set δ : ValueGroupWithZero k := (γ : ValueGroupWithZero k) * valuation k ϖ
  have hδ0 : δ ≠ 0 := mul_ne_zero γ.ne_zero (by simpa using hϖ0)
  have hδγ : δ < γ := mul_lt_of_lt_one_right (zero_lt_iff.mpr γ.ne_zero) hϖ1
  set N : Set (Matrix (Fin (r + t)) (Fin r) k) := {x | ∀ i j, valuation k (x i j - e i j) ≤ δ}
  have hNpi : N = Set.pi Set.univ fun i => Set.pi Set.univ fun j => {z : k | valuation k (z - e i j) ≤ δ} :=
    Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
  have hNc : IsCompact N := by
    rw [hNpi]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_vle_sub δ (e i j)
  have hNo : IsOpen N := by
    have : N = ⋂ i, ⋂ j, (fun x : Matrix (Fin (r + t)) (Fin r) k => x i j - e i j) ⁻¹' {z : k | valuation k z ≤ δ} := by
      ext x; simp [N]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (isOpen_vle hδ0).preimage ((Continuous.matrix_elem continuous_id i j).sub continuous_const)
  have hNcl : IsClosed N := hNc.isClosed
  have heN : e ∈ N := fun i j => by simp
  have hNP : ∀ x ∈ N, topRows r t x ∈ W := by
    intro x hx
    have : x - e ∈ I.pi fun _ => J.pi fun _ => {z : k | valuation k z < γ} :=
      fun i _ j _ => lt_of_le_of_lt (by simpa using hx i j) hδγ
    simpa using hsub this
  classical
  refine ⟨N.indicator 1, ⟨?_, ?_⟩, by simp [heN], fun x => ?_, fun g hg => ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ N
    · exact ⟨N, hNo, hx, fun y hy => by simp [hx, hy]⟩
    · exact ⟨Nᶜ, hNcl.isOpen_compl, hx, fun y hy => by simp [hx, Set.indicator_of_notMem hy]⟩
  · exact HasCompactSupport.intro' hNc hNcl fun x hx => Set.indicator_of_notMem hx _
  · by_cases hx : x ∈ N <;> simp [hx]
  · have hm : e * g.val ∈ N := by
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    have := hNP _ hm
    rw [topRows_eMat_mul] at this
    exact hWS g this
end GlobalTheory.GodementJacquet.TestNearE
