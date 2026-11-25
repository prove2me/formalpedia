-- Prove2me | solution 1 for GlobalTheory.Chamber.IsOrth.sub_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:34:26.494154+00:00
-- url     : https://prove2.me/submissions/1f19776f-588d-412c-8ad7-ff1150115ea3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_InverseChamberMap
import Theorems.Thm_GlobalTheory_Chamber_mem_parP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical
open GlobalTheory GlobalTheory.Chamber
variable {k : ℕ}
namespace GlobalTheory.Chamber
namespace IsOrth
theorem _root_.solution {𝔞 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) {P P' : Finset (SV k)}
    (hP : P ∈ parP 𝔞 ∅) (hP' : P' ∈ parP 𝔞 ∅) {u : SV k} (hu : u ∈ P) (e : P.erase u ⊆ P') :
    X P - X P' ∈ Submodule.span ℝ {rt P u} := by
  obtain ⟨h1, h2, -⟩ := mem_parP.1 hP
  obtain ⟨h1', h2', -⟩ := mem_parP.1 hP'
  have hF := mem_parF.2 ⟨h1, h2.le, empty_subset P⟩
  have hF' := mem_parF.2 ⟨h1', h2'.le, empty_subset P'⟩
  have hm : X P - X P' ∈ aP P := sub_mem (h P hF P subset_rfl ▸ Submodule.starProjection_apply_mem _ _)
    (h2 ▸ h2' ▸ h P' hF' P' subset_rfl ▸ Submodule.starProjection_apply_mem _ _)
  have h0 : pr (P.erase u) (X P - X P') = 0 := by rw [map_sub, ← h P hF _ (erase_subset _ _), ← h P' hF' _ e, sub_self]
  rw [aP, ← insert_erase hu, coe_insert, Set.image_insert_eq, Submodule.mem_span_insert, insert_erase hu] at hm
  obtain ⟨c, y, hy, e⟩ := hm
  refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
  rw [e, map_add, map_smul, show pr (P.erase u) y = y from Submodule.starProjection_eq_self_iff.2 hy] at h0
  rw [e, rt, wt, smul_sub, sub_eq_add_neg, neg_eq_of_add_eq_zero_right h0]
end IsOrth
end GlobalTheory.Chamber
