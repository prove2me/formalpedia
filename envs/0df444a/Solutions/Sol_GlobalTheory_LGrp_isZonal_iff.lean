-- Prove2me | solution 1 for GlobalTheory.LGrp.isZonal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:58.840888+00:00
-- url     : https://prove2.me/submissions/605d4a6a-3dd5-4418-95c4-a4187a69299c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_mem_fixed
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
open ValuativeRel
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.LGrp
theorem _root_.solution (ρ : Representation ℂ G V) (K : Subgroup G) (ω : G → ℂ) : IsZonal ρ K ω ↔ SmGL.IsZonal ρ K ω := by
  have key : ∀ l : Module.Dual ℂ V, l ∈ fixed ρ.dual K ↔ ∀ k ∈ K, ∀ x, l (ρ k x) = l x := fun l => by
    rw [mem_fixed]
    constructor
    · intro h k hk x
      simpa [Module.Dual.transpose_apply] using LinearMap.congr_fun (h k⁻¹ (inv_mem hk)) x
    · intro h k hk
      exact LinearMap.ext fun x => h k⁻¹ (inv_mem hk) x
  constructor
  · rintro ⟨v, hv, l, hl, h1, rfl⟩
    exact ⟨v, hv, l, (key l).2 hl, h1, fun _ => rfl⟩
  · rintro ⟨v, hv, l, hl, h1, h⟩
    exact ⟨v, hv, l, (key l).1 hl, h1, funext h⟩
end GlobalTheory.LGrp
