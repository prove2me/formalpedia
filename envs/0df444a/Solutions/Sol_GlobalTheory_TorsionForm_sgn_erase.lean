-- Prove2me | solution 1 for GlobalTheory.TorsionForm.sgn_erase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:15.643493+00:00
-- url     : https://prove2.me/submissions/64afc366-46a2-43b5-add9-6c6d1d3d15c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsTorsionFormPoint_049da9a0b6d9fde7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
open GlobalTheory GlobalTheory.TorsionForm
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
  (h : Pt E g → ℝ) (β : Fin n → E)
namespace GlobalTheory.TorsionForm
theorem _root_.solution {m : ℕ} (i : Fin m) (S : Finset (Fin m)) : sgn i (S.erase i) = sgn i S := by
  unfold sgn; congr 2; ext x; simp only [Finset.mem_filter, Finset.mem_erase]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.ne, h.1⟩, h.2⟩⟩
end GlobalTheory.TorsionForm
