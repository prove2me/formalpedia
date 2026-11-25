-- Prove2me | solution 1 for GroundTheory.PAdicHodge.fontaineTheta_map_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:42.47743+00:00
-- url     : https://prove2.me/submissions/9eb6439c-c26a-4fbb-a4a2-3416a5f8003a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Theorems.Thm_GroundTheory_PAdicHodge_untiltPreTiltMap_symm
import Theorems.Thm_GroundTheory_PAdicHodge_fontaineTheta_map_preTiltMap


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
theorem _root_.solution (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (u : WittVector p (integerTilt K C p N)) :
    ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u) :
        normInteger C) : C) =
      ((WittVector.fontaineTheta (normInteger (untiltField K C p N)) p
          (WittVector.map (preTiltUntiltEquiv N).symm.toRingHom u) :
        normInteger (untiltField K C p N)) : untiltField K C p N) := by
  have hu : WittVector.map (integerTilt K C p N).subtype u =
      WittVector.map (untiltPreTiltMap N) (WittVector.map (preTiltUntiltEquiv N).symm.toRingHom u) := by
    rw [← wittVector_map_comp]
    exact WittVector.ext fun n => (untiltPreTiltMap_symm N (u.coeff n)).symm
  rw [hu, untiltPreTiltMap, fontaineTheta_map_preTiltMap, coe_integerMap]
  rfl
end GroundTheory.PAdicHodge
