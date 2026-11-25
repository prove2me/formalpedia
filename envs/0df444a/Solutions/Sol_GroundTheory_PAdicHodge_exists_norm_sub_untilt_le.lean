-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_norm_sub_untilt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:20.199421+00:00
-- url     : https://prove2.me/submissions/e62b85ed-3d44-437f-b996-7a8666ca669b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltDegree
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Theorems.Thm_GroundTheory_PAdicHodge_tiltIntermediateField_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mk_untilt_eq
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_algebra
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] {y : C}
    (hy : y ∈ untiltField K C p N) (hy1 : ‖y‖ ≤ 1) :
    ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖ := by
  set F := untiltField K C p N
  obtain ⟨b, hb⟩ := exists_mk_untilt_eq (K := F) (p := p) ⟨⟨y, hy⟩, mem_normInteger.2 hy1⟩
  rw [mk_eq_mk_iff_norm_sub_le] at hb
  set a := preTiltMap p (F.val : F →+* C) (norm_val F) b
  have hacoe : ((PreTilt.untilt a : normInteger C) : C) =
      (((PreTilt.untilt b : normInteger F) : F) : C) :=
    coe_untilt_preTiltMap _ _ b
  have haN : a ∈ integerTilt K C p N := by
    rw [mem_integerTilt, ← tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N]
    refine ⟨algebraMap _ _ b, ?_⟩
    rw [tiltInclusion, tiltMap_algebraMap]
  refine ⟨a, haN, ?_⟩
  rw [hacoe, norm_sub_rev]
  have hpF : ‖(p : F)‖ = ‖(p : K)‖ := by
    change ‖((p : F) : C)‖ = _
    rw [show ((p : F) : C) = (p : C) from map_natCast F.val p, norm_natCast_algebra (K := K)]
  rw [← hpF]
  exact hb
end GroundTheory.PAdicHodge
