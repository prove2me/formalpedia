-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.mem_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:23.091926+00:00
-- url     : https://prove2.me/submissions/0c743085-809d-4ed2-bd8f-b9e31903313c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_Base_mem_of_coprime


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
theorem _root_.solution (Λ : _root_.GlobalTheory.SW.Lt E n) {u w : ℕ}
    (h : u.Coprime w) {v : Fin n → E}
    (hu : (u : E) • v ∈ Λ) (hw : (w : E) • v ∈ Λ) : v ∈ Λ :=
  _root_.GlobalTheory.SW.Base.mem_of_coprime Λ h hu hw
end _root_.GlobalTheory.SW.TwistAdm
end GlobalTheory.SW.TwistAdm
