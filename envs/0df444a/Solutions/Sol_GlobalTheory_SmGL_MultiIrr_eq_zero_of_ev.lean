-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.eq_zero_of_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:02.93545+00:00
-- url     : https://prove2.me/submissions/507cf750-6346-4dca-a82b-812336b517e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_coord_lTensor
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_exists_sum_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {F G H M V W U : Type} [Field F] [Group G] [Group H] [Group M] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
omit [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution {P : Subgroup H} (ρ : Representation F P W) (t : V ⊗[F] smoothPart (ind P ρ))
    (h : ∀ x, (ev ρ x).lTensor V t = 0) : t = 0 := by
  obtain ⟨s, -, h2⟩ := exists_sum_coord (Module.Basis.ofVectorSpace F V) t
  rw [h2 s le_rfl]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : coord ((Module.Basis.ofVectorSpace F V).coord i) _ t = 0 :=
    Subtype.ext (Subtype.ext (funext fun x => by
      have := coord_lTensor ((Module.Basis.ofVectorSpace F V).coord i) (ev ρ x) t
      rw [h, map_zero] at this
      exact this.symm))
  rw [this, TensorProduct.tmul_zero]
end GlobalTheory.SmGL.MultiIrr
