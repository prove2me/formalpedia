-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ringHom_frobeniusEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:31.052311+00:00
-- url     : https://prove2.me/submissions/405a51ea-fa14-445d-929a-5505f64d7305

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr

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
    [CharP S p] [PerfectRing R p] [PerfectRing S p] (f : R →+* S) (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := by
  apply (frobeniusEquiv S p).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
    frobeniusEquiv_symm_pow_p]
end GroundTheory.PAdicHodge
