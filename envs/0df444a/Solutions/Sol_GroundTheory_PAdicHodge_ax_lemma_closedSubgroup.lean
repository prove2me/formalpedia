-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ax_lemma_closedSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:09.02273+00:00
-- url     : https://prove2.me/submissions/479cb0d5-6aa8-4ee8-87af-eb99be0ca7fe

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_ax_lemma

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
theorem _root_.solution (H : Subgroup Gal(PadicAlgCl p/K))
    (hH : IsClosed (H : Set Gal(PadicAlgCl p/K))) (z : PadicAlgCl p) {r : ℝ}
    (hz : ∀ σ ∈ H, ‖σ z - z‖ ≤ r) :
    ∃ y ∈ IntermediateField.fixedField H, ‖z - y‖ ≤ axConstant p * r := by
  set L := (IntermediateField.fixedField H).restrictScalars ℚ_[p] with hL
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hH⟩
  have hτ : ∀ τ : Gal(PadicAlgCl p/L), ‖τ z - z‖ ≤ r := by
    intro τ
    let σ : Gal(PadicAlgCl p/K) :=
      { τ.toRingEquiv with
        commutes' := fun k => τ.commutes ⟨algebraMap K (PadicAlgCl p) k,
          (IntermediateField.mem_restrictScalars _).2
            (IntermediateField.algebraMap_mem _ k)⟩ }
    have hσ : σ ∈ H := by
      rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
      intro m hm
      exact τ.commutes ⟨m, (IntermediateField.mem_restrictScalars _).2 hm⟩
    exact hz σ hσ
  obtain ⟨y, hy, hle⟩ := ax_lemma z hτ
  exact ⟨y, (IntermediateField.mem_restrictScalars _).1 hy, hle⟩
end GroundTheory.PAdicHodge
