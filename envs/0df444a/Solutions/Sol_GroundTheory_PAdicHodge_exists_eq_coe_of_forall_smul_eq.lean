-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_eq_coe_of_forall_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:58:35.769082+00:00
-- url     : https://prove2.me/submissions/80ea0dc1-60a0-4ae7-a970-18593ed6bf4a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_fixedPoints_gal_eq

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
theorem _root_.solution [FiniteDimensional ℚ_[p] K] {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) :
    ∃ k : K, ((k : PadicAlgCl p) : ℂ_[p]) = x := by
  have : x ∈ MulAction.fixedPoints Gal(PadicAlgCl p/K) ℂ_[p] := hx
  rw [fixedPoints_gal_eq] at this
  obtain ⟨y, hy, rfl⟩ := this
  exact ⟨⟨y, hy⟩, rfl⟩
end GroundTheory.PAdicHodge
