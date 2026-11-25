-- Prove2me | solution 1 for GroundTheory.PAdicHodge.eq_sum_towerCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:11.418196+00:00
-- url     : https://prove2.me/submissions/1284b83a-c215-40c5-b0ff-fb58206b0b38

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_mono
import Theorems.Thm_GroundTheory_PAdicHodge_relDeg_eq_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_relDeg_pos
import Theorems.Thm_GroundTheory_PAdicHodge_towerVec_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_sum_towerVec_mul
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {m : ℕ} (hm : stableIndex K ≤ m) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLayer K m) : y = ∑ i, towerCoeff K m y i * towerVec K i := by
  set d := relDeg K (stableIndex K)
  let L := extendScalars (cycl_le_cyclotomicLayer K m)
  have hv : ∀ i, towerVec K i ∈ L := fun i => cyclotomicLayer_mono K hm (towerVec_mem K i)
  let v : Fin d → L := fun i => ⟨towerVec K i, hv i⟩
  have hd0 : (d : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 (relDeg_pos K _).ne'
  have hli : LinearIndependent (cycl p m) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 : (∑ i, (g i : PadicAlgCl p) * towerVec K i) = 0 := by
      have := congrArg (fun x : L => (x : PadicAlgCl p)) hg
      simpa [v, Algebra.smul_def] using this
    have h2 := normTrace_sum_towerVec_mul K hm (fun i => (g i : PadicAlgCl p)) (fun i => (g i).2) j
    rw [h1, zero_mul, normTrace_zero, eq_comm, div_eq_zero_iff] at h2
    exact Subtype.ext (h2.resolve_right hd0)
  have hcard : Fintype.card (Fin d) = finrank (cycl p m) L := by
    rw [Fintype.card_fin]
    exact (relDeg_eq_of_le K hm).symm
  haveI : Nonempty (Fin d) := ⟨⟨0, relDeg_pos K _⟩⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hsum := B.sum_repr ⟨y, hy⟩
  have hyexp : y = ∑ i, ((B.repr ⟨y, hy⟩ i : cycl p m) : PadicAlgCl p) * towerVec K i := by
    have := congrArg (fun x : L => (x : PadicAlgCl p)) hsum
    simpa [B, v, Algebra.smul_def] using this.symm
  have hc : ∀ j, ((B.repr ⟨y, hy⟩ j : cycl p m) : PadicAlgCl p) = towerCoeff K m y j := by
    intro j
    have := normTrace_sum_towerVec_mul K hm _ (fun i => (B.repr ⟨y, hy⟩ i).2) j
    rw [← hyexp] at this
    rw [towerCoeff, this]
    exact (mul_div_cancel₀ _ hd0).symm
  conv_lhs => rw [hyexp]
  simp_rw [hc]
  rfl
end GroundTheory.PAdicHodge
