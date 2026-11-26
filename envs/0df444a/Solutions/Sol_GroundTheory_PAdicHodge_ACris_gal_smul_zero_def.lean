-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.gal_smul_zero_def
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:08:10.673911+00:00
-- url     : https://prove2.me/submissions/19926095-ba5a-42cf-bd4d-5e623386ceb6

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
theorem solution (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    σ • y = galZero σ y := by
  rfl
