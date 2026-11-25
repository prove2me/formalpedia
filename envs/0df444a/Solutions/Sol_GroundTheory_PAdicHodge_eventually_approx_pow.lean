-- Prove2me | solution 1 for GroundTheory.PAdicHodge.eventually_approx_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:05.193646+00:00
-- url     : https://prove2.me/submissions/fe790854-5ffe-44eb-b5d8-94cb91744433

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_p_lt_one
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_p_pos
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_le_max_of_ultrametric
import Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_sub_pow_le
import Theorems.Thm_GroundTheory_PAdicHodge_exists_approx_of_pow_sub
import Theorems.Thm_GroundTheory_PAdicHodge_exists_lt_norm_pow_sub_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) (m : ℕ) :
    ∃ K : ℕ, ∀ k ≥ K, ∃ u ∈ unramifiedClosure p,
      ‖c ^ p ^ k - (u : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
  set δ := ‖(p : ℂ_[p])‖ ^ m
  have hδ : 0 < δ := pow_pos norm_natCast_p_pos m
  have hδ1 : δ ≤ 1 := pow_le_one₀ (norm_nonneg _) norm_natCast_p_lt_one.le
  obtain ⟨c', hc'⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)).exists_dist_lt c hδ
  rw [dist_eq_norm] at hc'
  have hc'1 : ‖(c' : ℂ_[p])‖ ≤ 1 := by
    have e : (c' : ℂ_[p]) = c - (c - c') := by ring
    rw [e]
    exact (norm_sub_le_max_of_ultrametric _ _).trans (max_le hc (hc'.le.trans hδ1))
  have hc'1' : ‖c'‖ ≤ 1 := by rwa [PadicComplex.norm_extends] at hc'1
  obtain ⟨k₀, k₁, hlt, hnear⟩ := exists_lt_norm_pow_sub_lt hc'1' hδ (fun k => p ^ k)
  have hnear' : ‖(c' : ℂ_[p]) ^ p ^ k₁ - (c' : ℂ_[p]) ^ p ^ k₀‖ < δ := by
    have e : (c' : ℂ_[p]) ^ p ^ k₁ - (c' : ℂ_[p]) ^ p ^ k₀ = ((c' ^ p ^ k₁ - c' ^ p ^ k₀ : PadicAlgCl p) : ℂ_[p]) := by
      simp only [UniformSpace.Completion.coe_sub, PadicComplex.coe_eq, map_pow]
    rw [e, PadicComplex.norm_extends]
    exact hnear
  refine ⟨k₀, fun k hk => ?_⟩
  set r := k₁ - k₀
  have hr : 1 ≤ r := by omega
  set z := c ^ p ^ k
  have hz : ‖z‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
  have hzq : z ^ p ^ r = c ^ p ^ (k + r) := by rw [← pow_mul, ← pow_add]
  have hkr : k + r = k₁ + (k - k₀) := by omega
  have hk' : k = k₀ + (k - k₀) := by omega
  have hA : ‖c ^ p ^ (k + r) - (c' : ℂ_[p]) ^ p ^ (k + r)‖ < δ :=
    (norm_pow_sub_pow_le hc hc'1 _).trans_lt hc'
  have hB : ‖(c' : ℂ_[p]) ^ p ^ (k + r) - (c' : ℂ_[p]) ^ p ^ k‖ < δ := by
    have e1 : (c' : ℂ_[p]) ^ p ^ (k + r) = ((c' : ℂ_[p]) ^ p ^ k₁) ^ p ^ (k - k₀) := by
      rw [← pow_mul, ← pow_add, hkr]
    have e2 : (c' : ℂ_[p]) ^ p ^ k = ((c' : ℂ_[p]) ^ p ^ k₀) ^ p ^ (k - k₀) := by
      rw [← pow_mul, ← pow_add, ← hk']
    rw [e1, e2]
    refine (norm_pow_sub_pow_le ?_ ?_ _).trans_lt hnear' <;>
      · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc'1
  have hC : ‖(c' : ℂ_[p]) ^ p ^ k - c ^ p ^ k‖ < δ := by
    rw [← norm_neg, neg_sub]
    exact (norm_pow_sub_pow_le hc hc'1 _).trans_lt hc'
  have hsum : ‖z ^ p ^ r - z‖ ≤ δ := by
    have e : z ^ p ^ r - z = (c ^ p ^ (k + r) - (c' : ℂ_[p]) ^ p ^ (k + r)) +
        (((c' : ℂ_[p]) ^ p ^ (k + r) - (c' : ℂ_[p]) ^ p ^ k) + ((c' : ℂ_[p]) ^ p ^ k - c ^ p ^ k)) := by
      rw [hzq]; ring
    rw [e]
    exact ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA.le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hB.le hC.le))))
  exact exists_approx_of_pow_sub hz hr hsum
end GroundTheory.PAdicHodge
