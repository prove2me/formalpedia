-- Prove2me | solution 1 for GlobalTheory.SW.Emb.botSpan_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:32.325733+00:00
-- url     : https://prove2.me/submissions/daf19333-6dae-4b9d-a9c8-5880e9d746af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.Emb
theorem _root_.solution {m : ℕ} (a d : Matrix (Fin m) (Fin m) E) (g : M2 E m) :
    botSpan (Matrix.fromBlocks a 0 0 d * g) ≤ botSpan g := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have e : (Matrix.fromBlocks a 0 0 d * g) (Sum.inr i) = ∑ k, d i k • g (Sum.inr k) := by
    ext j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply]
  show (Matrix.fromBlocks a 0 0 d * g) (Sum.inr i) ∈ botSpan g
  rw [e]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
end GlobalTheory.SW.Emb
