-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.evalB_toBDeRhamPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:22.084799+00:00
-- url     : https://prove2.me/submissions/01c67b67-182a-437e-a863-96ebc134ca0f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois

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
open Ideal WittVector IsLocalRing
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger K) p)
omit [CharZero K]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (n : ℕ) (a : 𝔸) :
    evalB K p n (toBDeRhamPlus 𝒪 p a) = Ideal.Quotient.mk (J ^ n) a := by
  change AdicCompletion.evalₐ J n (algebraMap 𝔸 (AdicCompletion J 𝔸) a) = _
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of]
end GroundTheory.PAdicHodge.IsPerfectoidField
