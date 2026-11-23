-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.colsIn_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:39.607808+00:00
-- url     : https://prove2.me/submissions/19b6cc15-621d-4a5f-a8e1-20fbe824bad7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_TwistAdm_col_eq

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
theorem _root_.solution {Λ : _root_.GlobalTheory.SW.Lt E n}
    {y : Matrix (Fin n) (Fin N) E} (h : _root_.GlobalTheory.SW.ColsIn Λ y)
    {v : Fin N → E} (hv : v ∈ _root_.GlobalTheory.SW.stdL E N) : y *ᵥ v ∈ Λ := by
  unfold _root_.GlobalTheory.SW.stdL at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    rw [← _root_.GlobalTheory.SW.TwistAdm.col_eq]
    exact h a
  | zero => simp [Λ.zero_mem]
  | add u w _ _ hu hw =>
    rw [Matrix.mulVec_add]
    exact Λ.add_mem hu hw
  | smul r w _ hw =>
    rw [Matrix.mulVec_smul]
    exact Λ.smul_mem r hw
end _root_.GlobalTheory.SW.TwistAdm
end GlobalTheory.SW.TwistAdm
