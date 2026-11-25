-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_approx_of_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:08.061979+00:00
-- url     : https://prove2.me/submissions/f813dcd5-a3e5-4e5a-9849-b6866cae8cf9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_p_lt_one
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_of_pow_eq_self
import Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_pow_sub_pow_pow_le

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
theorem _root_.solution {z : ℂ_[p]} (hz : ‖z‖ ≤ 1) {r m : ℕ} (hr : 1 ≤ r)
    (h : ‖z ^ p ^ r - z‖ ≤ ‖(p : ℂ_[p])‖ ^ m) :
    ∃ u ∈ unramifiedClosure p, ‖z - (u : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, zero_mem _, by simpa using hz⟩
  have hp1 : ‖(p : ℂ_[p])‖ ≤ 1 := norm_natCast_p_lt_one.le
  set q := p ^ r
  set u : ℕ → ℂ_[p] := fun j => z ^ q ^ j with hu
  have hnorm : ∀ j, ‖u j‖ ≤ 1 := fun j => by
    simp only [hu, norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  have hsucc : ∀ j, u (j + 1) = u j ^ q := fun j => by simp only [hu, pow_succ, pow_mul]
  have hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ ‖(p : ℂ_[p])‖ ^ (m + j) := by
    intro j
    induction j with
    | zero => simpa [hu, q] using h
    | succ j ih =>
      have key := norm_pow_pow_sub_pow_pow_le (hnorm (j + 1)) (hnorm j) hp1 (by omega) ih r
      have e1 : u (j + 1) ^ p ^ r = u (j + 1 + 1) := (hsucc (j + 1)).symm
      have e2 : u j ^ p ^ r = u (j + 1) := (hsucc j).symm
      rw [e1, e2] at key
      exact key.trans
        (pow_le_pow_of_le_one (norm_nonneg _) hp1 (show m + (j + 1) ≤ m + j + r by omega))
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_geometric ‖(p : ℂ_[p])‖ (‖(p : ℂ_[p])‖ ^ m) norm_natCast_p_lt_one
      fun j => ?_
    rw [dist_comm, dist_eq_norm, ← pow_add]
    exact hstep j
  obtain ⟨ω, hω⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hclose : ∀ j, ‖u j - z‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
    intro j
    induction j with
    | zero => simp [hu]
    | succ j ih =>
      have e : u (j + 1) - z = (u (j + 1) - u j) + (u j - z) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hstep j).trans
        (pow_le_pow_of_le_one (norm_nonneg _) hp1 (by omega))) ih)
  have hωz : ‖ω - z‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
    have ht : Tendsto (fun j => ‖u j - z‖) atTop (𝓝 ‖ω - z‖) :=
      (continuous_norm.tendsto _).comp (hω.sub_const z)
    exact le_of_tendsto ht (Eventually.of_forall hclose)
  have hfix : ω ^ q = ω := by
    have h1 : Tendsto (fun j => u j ^ q) atTop (𝓝 (ω ^ q)) := hω.pow q
    have h2 : Tendsto (fun j => u j ^ q) atTop (𝓝 ω) := by
      simp_rw [← hsucc]
      exact (tendsto_add_atTop_iff_nat 1).2 hω
    exact tendsto_nhds_unique h1 h2
  obtain ⟨v, hv, hvω⟩ := exists_eq_of_pow_eq_self hr hfix
  refine ⟨v, hv, ?_⟩
  rw [hvω, ← norm_neg, neg_sub]
  exact hωz
end GroundTheory.PAdicHodge
