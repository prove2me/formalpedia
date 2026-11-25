-- Prove2me | solution 1 for GroundTheory.PAdicHodge.gal_smul_mem_padicComplexInt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:18.866391+00:00
-- url     : https://prove2.me/submissions/bc22309f-5654-4205-881a-b658a925add8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Theorems.Thm_GroundTheory_PAdicHodge_mem_padicComplexInt_iff

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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    σ • x ∈ 𝓞_ℂ_[p] ↔ x ∈ 𝓞_ℂ_[p] := by
  rw [mem_padicComplexInt_iff, mem_padicComplexInt_iff, norm_smul_gal]
end GroundTheory.PAdicHodge
