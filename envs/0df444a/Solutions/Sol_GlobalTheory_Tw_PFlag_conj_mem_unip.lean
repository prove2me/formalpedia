-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.conj_mem_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:31.780349+00:00
-- url     : https://prove2.me/submissions/24ad12f0-9410-495a-8416-fe73753335dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_conj_mem_lieN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
open GlobalTheory.Tw.PFlag
variable {n : ℕ} {k : Type} [CommRing k] (F : PFlag n k)
variable {F}
variable (F)
variable {F}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution {g u : GL (Fin n) k} (hg : g ∈ F.stab) (hu : u ∈ F.unip) : g * u * g⁻¹ ∈ F.unip :=
  ⟨mul_mem (mul_mem hg hu.1) (inv_mem hg), by
    have : (g * u * g⁻¹).val - 1 = g.val * (u.val - 1) * g⁻¹.val := by
      rw [mul_sub, sub_mul, mul_one, Units.mul_inv]; rfl
    rw [this]; exact conj_mem_lieN hg hu.2⟩
end GlobalTheory.Tw.PFlag
