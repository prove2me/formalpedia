-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.eq_zero_of_forall_mem_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:48.339139+00:00
-- url     : https://prove2.me/submissions/dcf29bab-eb34-4476-949b-41cfdc4d84a6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isAdicComplete_maximalIdeal_bDeRhamPlus


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
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {x : 𝔹} (h : ∀ n : ℕ, x ∈ maximalIdeal 𝔹 ^ n) :
    x = 0 := by
  have hc := isAdicComplete_maximalIdeal_bDeRhamPlus (K := K) (p := p)
  refine hc.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact h n
end GroundTheory.PAdicHodge.IsPerfectoidField
