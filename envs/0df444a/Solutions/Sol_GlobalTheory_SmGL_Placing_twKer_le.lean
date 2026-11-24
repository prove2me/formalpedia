-- Prove2me | solution 1 for GlobalTheory.SmGL.Placing.twKer_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:21.529829+00:00
-- url     : https://prove2.me/submissions/8a633bbe-66ba-4586-a43b-1678207a03ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Placing
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]
open ValuativeRel MeasureTheory
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]
namespace GlobalTheory.SmGL.Placing
namespace _root_.GlobalTheory.SmGL.Placing
theorem _root_.solution (π : Representation F G V)
    {N N' : Subgroup G} (w : G) (h : ∀ u ∈ N, w * u * w⁻¹ ∈ N') :
    _root_.GlobalTheory.PRep.twKer π N 1 ≤ (_root_.GlobalTheory.PRep.twKer π N' 1).comap (π w) := by
  unfold _root_.GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  rintro _ ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  refine Submodule.subset_span ⟨⟨w * u * w⁻¹, h u u.2⟩, π w v, ?_⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, map_mul, Module.End.mul_apply]
  rw [← Module.End.mul_apply (π w⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
end _root_.GlobalTheory.SmGL.Placing
end GlobalTheory.SmGL.Placing
