-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.single_mem_std
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:52.834388+00:00
-- url     : https://prove2.me/submissions/5413e524-740b-4938-8dfc-8e29b093b1be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.TwistAdm
namespace _root_.GlobalTheory.SW.TwistAdm
theorem _root_.solution (a : Fin N) :
    (Pi.single a 1 : Fin N → E) ∈ _root_.GlobalTheory.SW.stdL E N := by
  unfold _root_.GlobalTheory.SW.stdL
  exact Submodule.subset_span ⟨a, rfl⟩
end _root_.GlobalTheory.SW.TwistAdm
end GlobalTheory.SW.TwistAdm
