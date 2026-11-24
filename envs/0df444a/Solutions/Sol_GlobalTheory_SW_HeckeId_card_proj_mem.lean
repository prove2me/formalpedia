-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.card_proj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:45:32.279496+00:00
-- url     : https://prove2.me/submissions/55693e56-e810-4526-b56e-0f398bcb717c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_card_lines_le_submodule


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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution (F V : Type) [Field F] [AddCommGroup V] [Module F V] [Finite V]
    (K : Submodule F V) :
    Nat.card {p : ℙ F V // p.rep ∈ K} * (Nat.card F - 1) + 1 = Nat.card K := by
  rw [← card_lines_le_submodule F V K]
  congr 2
  refine Nat.card_congr (((Projectivization.equivSubmodule F V).subtypeEquiv
    (q := fun l => l.1 ≤ K) fun p => ?_).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ (· ≤ K)))
  change _ ↔ p.submodule ≤ K
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
end GlobalTheory.SW.HeckeId
