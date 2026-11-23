-- Prove2me | solution 1 for GlobalTheory.CentralExponent.isOpen_cong
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:40.513825+00:00
-- url     : https://prove2.me/submissions/a186f75f-b25e-4535-a748-2a6798f68c41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IrreducibleTensorCharacter
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData ValuativeRel Matrix Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.CentralExponent
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CentralExponent
theorem _root_.solution (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) :
    IsOpen (cong n γ hγ : Set (GL n k)) := by
  have e : (cong n γ hγ : Set (GL n k)) = ⋂ i, ⋂ j,
      (fun g : GL n k => (g.val - 1) i j) ⁻¹' {x | valuation k x < γ} := by
    ext g; simp only [SetLike.mem_coe, Set.mem_iInter]; rfl
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · exact (Units.continuous_val.sub continuous_const).matrix_elem i j
  · refine isOpen_iff_mem_nhds.2 fun x hx => (IsValuativeTopology.mem_nhds_iff).2 ⟨γ, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact Valuation.map_add_lt (valuation k) (g := γ) hx hy
end GlobalTheory.CentralExponent
