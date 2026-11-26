-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.gal_smul_dpow
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T15:52:45.176883+00:00
-- url     : https://prove2.me/submissions/8e7e4ee6-31a9-4fb4-9f4d-87afcba8859c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.ACris
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger ℂ_[p]) p)

open GroundTheory.PAdicHodge.ACris in
theorem solution (σ : Gal(PadicAlgCl p/K)) {x : AInf ℂ_[p] p} (hx : x ∈ RingHom.ker θ)
    (n : ℕ) :
    σ • (⟨dpow n x, dpow_mem hx n⟩ : ACrisZero ℂ_[p] p) =
      ⟨dpow n (σ • x), dpow_mem (gal_smul_mem_ker σ hx) n⟩ := by
  refine Subtype.ext ?_
  change galAway σ (dpow n x) = dpow n (σ • x)
  exact galAway_dpow σ n x
