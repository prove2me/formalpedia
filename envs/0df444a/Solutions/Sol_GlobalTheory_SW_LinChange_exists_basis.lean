-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:11.873584+00:00
-- url     : https://prove2.me/submissions/33eb98cd-4385-4319-98e1-7def7c72ad66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.LinChange
theorem _root_.solution : ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
    (b : Module.Basis J ℚ (Matrix κ ι K)),
    ∀ x, x ∈ AddSubgroup.closure (Set.range b) ↔ IntM x := by
  classical
  refine ⟨_, inferInstance, inferInstance,
    (NumberField.integralBasis K).smulTower (Matrix.stdBasis K κ ι), fun x => ?_⟩
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Module.Basis.mem_span_iff_repr_mem]
  have key : ∀ a : K, IsIntegral ℤ a ↔
      ∀ j, (NumberField.integralBasis K).repr a j ∈ Set.range (algebraMap ℤ ℚ) := by
    intro a
    rw [← Module.Basis.mem_span_iff_repr_mem, NumberField.mem_span_integralBasis]
    exact ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨c, hc⟩ => hc ▸ c.2⟩
  have hr : ∀ p : κ × ι, (Matrix.stdBasis K κ ι).repr x p = x p.1 p.2 := by
    intro p
    simp [Matrix.stdBasis]
  simp only [IntM, key, Module.Basis.smulTower_repr, hr]
  exact ⟨fun h k i j => h (j, (k, i)), fun h p => h p.2.1 p.2.2 p.1⟩
end GlobalTheory.SW.LinChange
