-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.Hyp.smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:30.489802+00:00
-- url     : https://prove2.me/submissions/b5693941-68a2-4d53-adce-1ee0504e8773

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise

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
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
namespace GlobalTheory.SW.HeckeId
namespace Hyp
theorem _root_.solution {P : Ideal O} {N : Submodule O M} (h : N ∈ Hyp P M) {c : O} (hc : c ∈ P)
    (x : M) : c • x ∈ N := by
  obtain ⟨f, -, rfl⟩ := h
  rw [LinearMap.mem_ker, map_smul, Algebra.smul_def]
  have : algebraMap O (O ⧸ P) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
  rw [this, zero_mul]
end Hyp
end GlobalTheory.SW.HeckeId
