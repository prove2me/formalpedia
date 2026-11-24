-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.frobeniusEquiv_symm_ofCompatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:23.049363+00:00
-- url     : https://prove2.me/submissions/af0c7e59-86ac-4163-9beb-f76e55d2c882

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_coeff_ofCompatible
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_preTilt_ext


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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) :
    (_root_.frobeniusEquiv 𝒪♭ p).symm (IsPerfectoidField.ofCompatible p y hy) =
      IsPerfectoidField.ofCompatible p (fun n => y (n + 1)) (fun n => hy (n + 1)) :=
  IsPerfectoidField.preTilt_ext p fun n => by
    rw [PreTilt.coeff_frobeniusEquiv_symm, IsPerfectoidField.coeff_ofCompatible,
      IsPerfectoidField.coeff_ofCompatible]
end GroundTheory.PAdicHodge.AInf
