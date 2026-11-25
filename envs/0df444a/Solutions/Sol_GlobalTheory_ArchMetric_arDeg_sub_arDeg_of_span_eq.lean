-- Prove2me | solution 1 for GlobalTheory.ArchMetric.arDeg_sub_arDeg_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:27:03.397448+00:00
-- url     : https://prove2.me/submissions/466ed2c3-3923-4f35-9dfb-0c0408c52b31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A : Submodule (𝓞 K) V} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchMetric
theorem _root_.solution {B : Submodule (𝓞 K) V} (hA : A.FG) (hB : B.FG)
    (hAB : Submodule.span K (A : Set V) = Submodule.span K (B : Set V)) :
    h.arDeg A - h.arDeg B = Real.log (B.toAddSubgroup.relIndex A.toAddSubgroup) -
      Real.log (A.toAddSubgroup.relIndex B.toAddSubgroup) := by
  have hs : Submodule.span K ((A ⊓ B : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (A : Set V) := by
    rw [span_localization_inf K (nonZeroDivisors (𝓞 K)), ← hAB, inf_idem]
  have e1 : (A ⊓ B).toAddSubgroup = A.toAddSubgroup ⊓ B.toAddSubgroup := rfl
  rw [h.arDeg_eq_add_log_relIndex (B := A ⊓ B) hA inf_le_left
      fun x hx => hs.ge (Submodule.subset_span hx),
    h.arDeg_eq_add_log_relIndex (B := A ⊓ B) hB inf_le_right
      fun x hx => (hs.trans hAB).ge (Submodule.subset_span hx),
    e1, AddSubgroup.inf_relIndex_left, AddSubgroup.inf_relIndex_right]
  ring
end GlobalTheory.ArchMetric
