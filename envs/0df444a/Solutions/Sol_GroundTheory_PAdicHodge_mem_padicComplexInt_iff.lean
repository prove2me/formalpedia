-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mem_padicComplexInt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:00:07.65971+00:00
-- url     : https://prove2.me/submissions/9f737c7a-26b9-4e87-ada8-e1d4a5b770fc

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open UniformSpace Topology Filter
noncomputable section
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe,
    ← map_one (Valuation.RankOne.hom (PadicComplex.valued p).v),
    (Valuation.RankOne.strictMono _).le_iff_le, Valuation.restrict_le_one_iff]
  rfl
end GroundTheory.PAdicHodge
