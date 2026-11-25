-- Prove2me | solution 1 for GroundTheory.PAdicHodge.setOf_forall_smul_eq_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:28:08.515857+00:00
-- url     : https://prove2.me/submissions/47339a25-a00f-4719-9bca-2ae94a2c3b7e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_isClosed_setOf_forall_smul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
open UniformSpace Topology
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (S : Set Gal(PadicAlgCl p/K)) (L : Set (PadicAlgCl p))
    (hL : ∀ y ∈ L, ∀ σ ∈ S, σ y = y) {C : ℝ} (hC : 0 < C)
    (hax : ∀ z : PadicAlgCl p, ∀ r : ℝ, (∀ σ ∈ S, ‖σ z - z‖ ≤ r) → ∃ y ∈ L, ‖z - y‖ ≤ C * r) :
    {x : ℂ_[p] | ∀ σ ∈ S, σ • x = x} = closure (((↑) : PadicAlgCl p → ℂ_[p]) '' L) := by
  refine subset_antisymm ?_ (closure_minimal ?_ (isClosed_setOf_forall_smul_eq S))
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ := ε / (C + 1) with hδ
    have hδ0 : 0 < δ := div_pos hε (by linarith)
    have hδε : δ < ε := div_lt_self hε (by linarith)
    have hCδ : C * δ < ε := by
      rw [hδ, mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    obtain ⟨_, ⟨z, rfl⟩, hxz⟩ := Metric.mem_closure_iff.1
      (Completion.denseRange_coe (α := PadicAlgCl p) x) δ hδ0
    rw [dist_eq_norm] at hxz
    have hmove : ∀ σ ∈ S, ‖σ z - z‖ ≤ δ := by
      intro σ hσ
      rw [← PadicComplex.norm_extends, Completion.coe_sub, ← gal_smul_coe]
      have h1 : σ • (z : ℂ_[p]) - (z : ℂ_[p]) = σ • ((z : ℂ_[p]) - x) - ((z : ℂ_[p]) - x) := by
        rw [smul_sub, hx σ hσ]; abel
      rw [h1, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_smul_gal, norm_sub_rev]; exact hxz.le
      · rw [norm_neg, norm_sub_rev]; exact hxz.le
    obtain ⟨y, hyL, hy⟩ := hax z δ hmove
    refine ⟨(y : ℂ_[p]), ⟨y, hyL, rfl⟩, ?_⟩
    rw [dist_eq_norm, ← sub_add_sub_cancel x (z : ℂ_[p]) (y : ℂ_[p])]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hxz.trans hδε) ?_)
    rw [← Completion.coe_sub, PadicComplex.norm_extends]
    exact hy.trans_lt hCδ
  · rintro _ ⟨y, hy, rfl⟩ σ hσ
    rw [gal_smul_coe, hL y hy σ hσ]
end GroundTheory.PAdicHodge
