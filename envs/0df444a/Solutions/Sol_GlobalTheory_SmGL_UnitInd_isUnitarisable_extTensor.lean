-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.isUnitarisable_extTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:26.721222+00:00
-- url     : https://prove2.me/submissions/4f17b41e-9fd3-42bc-86ae-e226b6b70387

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution {ρ : Representation ℂ G V} {σ : Representation ℂ H W}
    (h₁ : IsUnitarisable ρ) (h₂ : IsUnitarisable σ) : IsUnitarisable (extTensor ρ σ) := by
  obtain ⟨B, b1, b2, b3⟩ := h₁
  obtain ⟨C, c1, c2, c3⟩ := h₂
  letI : InnerProductSpace.Core ℂ V := core B b1 b2
  letI : InnerProductSpace.Core ℂ W := core C c1 c2
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : NormedAddCommGroup W := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore _
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore _
  refine ⟨(innerₛₗ ℂ (E := V ⊗[ℂ] W)).flip, fun v w => (inner_conj_symm (𝕜 := ℂ) v w).symm, fun v hv => ?_, fun g v w => ?_⟩
  · exact (re_inner_self_pos (𝕜 := ℂ)).2 hv
  · show inner ℂ (extTensor ρ σ g w) (extTensor ρ σ g v) = inner ℂ w v
    induction v with
    | zero => simp
    | add x y hx hy => simp only [map_add, inner_add_right, hx, hy]
    | tmul v v' =>
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, inner_add_left, hx, hy]
      | tmul w w' =>
        rw [extTensor_tmul, extTensor_tmul, TensorProduct.inner_tmul, TensorProduct.inner_tmul]
        exact congrArg₂ _ (b3 _ _ _) (c3 _ _ _)
end GlobalTheory.SmGL.UnitInd
