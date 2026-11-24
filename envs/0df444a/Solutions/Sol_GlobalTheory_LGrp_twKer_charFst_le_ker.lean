-- Prove2me | solution 1 for GlobalTheory.LGrp.twKer_charFst_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:35:10.731804+00:00
-- url     : https://prove2.me/submissions/b62f6a28-5899-4171-b828-1639c80aca72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
variable {A G H V W : Type} [Group A] [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.LGrp
theorem _root_.solution (χ : A →* ℂˣ) (ρ : Representation ℂ (A × H) V) (f : V →ₗ[ℂ] W) :
    twKer ρ (MonoidHom.inl A H).range (charFst H χ) ≤ LinearMap.ker f ↔
      ∀ a v, f (ρ (a, 1) v) = (χ a : ℂ) • f v := by
  constructor
  · intro h a v
    have := h (Submodule.subset_span ⟨⟨(a, 1), a, rfl⟩, v, rfl⟩)
    rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
    exact this
  · intro h
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨_, a, rfl⟩, v, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero]
    exact h a v
end GlobalTheory.LGrp
