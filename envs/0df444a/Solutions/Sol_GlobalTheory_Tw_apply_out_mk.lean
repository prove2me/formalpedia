-- Prove2me | solution 1 for GlobalTheory.Tw.apply_out_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:55.092847+00:00
-- url     : https://prove2.me/submissions/a2fe1598-f400-4db4-a120-a22b9afb0198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {G : Type} [Group G] [MeasurableSpace G]
omit [MeasurableSpace G]
namespace GlobalTheory.Tw
theorem _root_.solution {T : Subgroup G} {α : Type} {F : G → α} (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) (x : G) :
    F (Quotient.out (Quotient.mk (QuotientGroup.rightRel T) x)) = F x := by
  have h := Quotient.mk_out (s := QuotientGroup.rightRel T) x
  rw [QuotientGroup.rightRel_apply] at h
  have := hF _ h (Quotient.out (Quotient.mk (QuotientGroup.rightRel T) x))
  rw [inv_mul_cancel_right] at this
  exact this.symm
end GlobalTheory.Tw
