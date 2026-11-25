-- Prove2me | solution 1 for GroundTheory.PAdicHodge.isClosed_setOf_forall_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:12.099795+00:00
-- url     : https://prove2.me/submissions/e137921e-a757-4638-9cc0-284f5c4076c9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

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
open Polynomial
noncomputable section
open UniformSpace Topology
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (S : Set Gal(PadicAlgCl p/K)) :
    IsClosed {x : ℂ_[p] | ∀ σ ∈ S, σ • x = x} := by
  have : {x : ℂ_[p] | ∀ σ ∈ S, σ • x = x} = ⋂ σ ∈ S, {x : ℂ_[p] | σ • x = x} := by
    ext x; simp
  rw [this]
  exact isClosed_biInter fun σ _ => isClosed_eq (continuous_const_smul σ) continuous_id
end GroundTheory.PAdicHodge
