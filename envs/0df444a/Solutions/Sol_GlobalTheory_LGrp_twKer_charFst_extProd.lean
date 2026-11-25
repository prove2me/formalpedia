-- Prove2me | solution 1 for GlobalTheory.LGrp.twKer_charFst_extProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:58:22.114006+00:00
-- url     : https://prove2.me/submissions/1f3d3903-02bd-4e8f-a00c-d2e9d72b687a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_twKer_charFst_le_ker
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
variable {A G H V W : Type} [Group A] [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.LGrp
theorem _root_.solution (χ χ' : A →* ℂˣ) (π : Representation ℂ H W) :
    (χ = χ' → twKer (extProd (charRep χ') π) (MonoidHom.inl A H).range (charFst H χ) = ⊥) ∧
      (χ ≠ χ' → twKer (extProd (charRep χ') π) (MonoidHom.inl A H).range (charFst H χ) = ⊤) := by
  have key : ∀ (a : A) (v : ℂ ⊗[ℂ] W), extProd (charRep χ') π (a, 1) v = (χ' a : ℂ) • v := by
    intro a v
    induction v with
    | zero => simp
    | tmul x w => simp [TensorProduct.smul_tmul']
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
  constructor
  · rintro rfl
    rw [eq_bot_iff, ← LinearMap.ker_id, twKer_charFst_le_ker]
    exact key
  · intro h
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h
    have hne : (χ' a : ℂ) - χ a ≠ 0 := sub_ne_zero.2 fun e => ha (Units.ext e.symm)
    refine eq_top_iff.2 fun v _ => Submodule.subset_span ⟨⟨(a, 1), a, rfl⟩, ((χ' a : ℂ) - χ a)⁻¹ • v, ?_⟩
    show v = extProd (charRep χ') π (a, 1) _ - (χ a : ℂ) • _
    rw [key, ← sub_smul, smul_inv_smul₀ hne]
end GlobalTheory.LGrp
