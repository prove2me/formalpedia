-- Prove2me | solution 1 for GlobalTheory.SmGL.CuspMax.subsingleton_jacquet_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:14.243826+00:00
-- url     : https://prove2.me/submissions/2c0e3448-b944-47b1-b34c-9e4e0c7671e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.CuspMax
namespace GlobalTheory.SmGL.CuspMax
theorem _root_.solution {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) {N N' : Subgroup G} (g : G) (h : ∀ u ∈ N, g * u * g⁻¹ ∈ N')
    (hN : Subsingleton (Jacquet π N)) : Subsingleton (Jacquet π N') := by
  have h1 : twKer π N 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 hN
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)
  have h2 : twKer π N 1 ≤ (twKer π N' 1).comap (π g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    refine Submodule.subset_span ⟨⟨_, h u u.2⟩, π g w, ?_⟩
    simp [← Module.End.mul_apply, ← map_mul]
  have h3 : π g⁻¹ v ∈ twKer π N 1 := h1 ▸ Submodule.mem_top
  have h4 : π g (π g⁻¹ v) ∈ twKer π N' 1 := h2 h3
  simpa [← Module.End.mul_apply, ← map_mul] using h4
end GlobalTheory.SmGL.CuspMax
