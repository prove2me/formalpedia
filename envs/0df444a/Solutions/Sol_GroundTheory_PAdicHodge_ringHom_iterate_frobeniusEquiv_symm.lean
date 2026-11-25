-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ringHom_iterate_frobeniusEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:14.451605+00:00
-- url     : https://prove2.me/submissions/13b4ce4f-c8be-4ca4-8e10-83a1ef22f26f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Theorems.Thm_GroundTheory_PAdicHodge_ringHom_frobeniusEquiv_symm

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
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] [CharP R p]
    [CharP S p] [PerfectRing R p] [PerfectRing S p] (f : R →+* S) (x : R) (n : ℕ) :
    f ((frobeniusEquiv R p).symm^[n] x) = (frobeniusEquiv S p).symm^[n] (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ringHom_frobeniusEquiv_symm, ih]
end GroundTheory.PAdicHodge
