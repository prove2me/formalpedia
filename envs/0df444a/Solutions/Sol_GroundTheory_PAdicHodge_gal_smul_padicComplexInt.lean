-- Prove2me | solution 1 for GroundTheory.PAdicHodge.gal_smul_padicComplexInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:34.952931+00:00
-- url     : https://prove2.me/submissions/92e09b2d-cb3e-4b84-92aa-c46269abbb32

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_mem_padicComplexInt_iff

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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) :
    (fun x : ℂ_[p] => σ • x) '' (𝓞_ℂ_[p] : Set ℂ_[p]) = 𝓞_ℂ_[p] := by
  ext x
  refine ⟨?_, fun hx => ⟨σ⁻¹ • x, ?_, smul_inv_smul σ x⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact (gal_smul_mem_padicComplexInt_iff σ y).2 hy
  · exact (gal_smul_mem_padicComplexInt_iff σ⁻¹ x).2 hx
end GroundTheory.PAdicHodge
