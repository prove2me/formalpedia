-- Prove2me | solution 1 for GlobalTheory.SmGL.Stages.tensor_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:25.156645+00:00
-- url     : https://prove2.me/submissions/efcbb56a-d9fd-4d53-a4cf-ed74d90db6ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
import Theorems.Thm_GlobalTheory_SmGL_Stages_coord_rTensor
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
variable {F G M W X Y Z : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]
namespace GlobalTheory.SmGL.Stages
theorem _root_.solution {P : Subgroup M} (σ : Representation F P W) (y : smoothPart (ind P σ) ⊗[F] X)
    (h : ∀ m, (evalAt σ m).rTensor X y = 0) : y = 0 := by
  classical
  let b := Module.Free.chooseBasis F X
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i m
  have := coord_rTensor b (evalAt σ m) y i
  rw [h] at this
  exact this.symm.trans (by simp)
end GlobalTheory.SmGL.Stages
