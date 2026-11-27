-- Prove2me | solution 2 for GroundTheory.PAdicHodge.Laurent.cmul_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:52.719311+00:00
-- url     : https://prove2.me/submissions/82553821-8354-4d72-b613-755397be2b8c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries

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
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
variable [CompleteSpace K]
namespace GroundTheory.PAdicHodge.Laurent
theorem _root_.solution (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) : cmul (cmul a b) c = cmul a (cmul b c) := by
  funext n
  simp only [cmul]
  have h1 : ∀ j, (∑' i, a i * b (j - i)) * c (n - j) = ∑' i, a i * b (j - i) * c (n - j) :=
    fun j => tsum_mul_right.symm
  have h2 : ∀ i, a i * ∑' k, b k * c (n - i - k) = ∑' j, a i * b (j - i) * c (n - j) := by
    intro i
    rw [← tsum_mul_left, ← (Equiv.subRight i).tsum_eq (fun k => a i * (b k * c (n - i - k)))]
    congr 1; funext j
    simp only [Equiv.subRight_apply]
    rw [show n - i - (j - i) = n - j by ring, mul_assoc]
  simp_rw [h1, h2]
  have hsum : Summable (Function.uncurry fun i j => a i * b (j - i) * c (n - j)) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h3 := tendsto_mul_cofinite_nhds_zero ha (tendsto_weight_prod hb hc)
    have hinj : Function.Injective (fun p : ℤ × ℤ => (p.1, (p.2 - p.1, n - p.2))) := by
      intro p q h
      simp only [Prod.mk.injEq] at h
      ext <;> omega
    have := (h3.comp hinj.tendsto_cofinite).div_const (ρ ^ n)
    rw [zero_div] at this
    refine this.congr fun ⟨i, j⟩ => ?_
    simp only [Function.comp, Function.uncurry_apply_pair, norm_mul]
    have hρ' := hρ.ne'
    have : ρ ^ n = ρ ^ i * ρ ^ (j - i) * ρ ^ (n - j) := by
      rw [← zpow_add₀ hρ', ← zpow_add₀ hρ']; congr 1; ring
    rw [this]
    field_simp
  exact hsum.tsum_comm
end GroundTheory.PAdicHodge.Laurent
