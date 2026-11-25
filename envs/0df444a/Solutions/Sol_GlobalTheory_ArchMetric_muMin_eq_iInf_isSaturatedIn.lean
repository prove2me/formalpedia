-- Prove2me | solution 1 for GlobalTheory.ArchMetric.muMin_eq_iInf_isSaturatedIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:31.218405+00:00
-- url     : https://prove2.me/submissions/3a5ae701-cbc6-4aa9-bc93-958931c64fc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_muMin_le_quotSlope
import Theorems.Thm_GlobalTheory_ArchMetric_le_muMin_iff
import Theorems.Thm_GlobalTheory_isSaturatedIn_iff_exists_subspace


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
variable {A B : Submodule (𝓞 K) V}
namespace GlobalTheory.ArchMetric
theorem _root_.solution (A : Submodule (𝓞 K) V) :
    h.muMin A = ⨅ (B : Submodule (𝓞 K) V) (_ : IsSaturatedIn A B) (_ : B ≠ A),
      (h.quotSlope A B : EReal) := by
  refine le_antisymm (le_iInf fun B => le_iInf fun hB => le_iInf fun hne => ?_)
    (h.le_muMin_iff.2 fun W hW => ?_)
  · obtain ⟨W, rfl⟩ := (isSaturatedIn_iff_exists_subspace K).1 hB
    exact h.muMin_le_quotSlope fun hW => hne (inf_eq_left.2 hW)
  · exact iInf_le_of_le _ (iInf_le_of_le (isSaturatedIn_inf_restrictScalars A W)
      (iInf_le_of_le (fun hW' => hW (inf_eq_left.1 hW')) le_rfl))
end GlobalTheory.ArchMetric
