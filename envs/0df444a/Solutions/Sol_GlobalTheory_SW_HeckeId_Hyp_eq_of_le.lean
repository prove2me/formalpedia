-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.Hyp.eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:46.483731+00:00
-- url     : https://prove2.me/submissions/114b70ea-de07-4e60-a615-568321f160e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_smul_mem
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_gen

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
theorem _root_.solution {P : Ideal O} [hP : P.IsMaximal] {N N' : Submodule O M} (h : N ∈ Hyp P M)
    (hle : N ≤ N') (hne : ¬ ∀ x, x ∈ N') : N = N' := by
  refine le_antisymm hle fun v hv => by_contra fun hv' => hne fun x => ?_
  obtain ⟨r, hr⟩ := Hyp.gen h hv' x
  simpa using N'.add_mem (hle hr) (N'.smul_mem r hv)
end Hyp
end GlobalTheory.SW.HeckeId
