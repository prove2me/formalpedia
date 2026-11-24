-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:32:57.248197+00:00
-- url     : https://prove2.me/submissions/bff21392-09d3-45d8-b883-577ed46ac7c1

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
namespace GlobalTheory.SW.TwistAdm
theorem _root_.solution (Λ : Lt E n) (k : ℤ) {v : Fin n → E} (h : v ∈ Λ) : (k : E) • v ∈ Λ := by
  rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem h k
end GlobalTheory.SW.TwistAdm
