-- Prove2me | solution 1 for GlobalTheory.TorusNormal.unip_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:36:11.373223+00:00
-- url     : https://prove2.me/submissions/98d61bd7-ae77-44d6-b3aa-0d6b188791c8

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_fIwasawa_mk_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.TorusNormal
open Formalism.UG.P
variable {L : Type} [Field L]
namespace GlobalTheory.TorusNormal
theorem _root_.solution {n : ℕ} (σ : L →+* L) (u : Fin n → L) (h : fIwasawaUn σ (pm 1 u))
    (hsupp : ∀ i, u i ≠ 0 → 2 * i.val + 1 < n) : IsUnipU (fIwasawaMk σ (pm 1 u) h) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [fIwasawa_mk_val]
    simp only [pm, Matrix.of_apply, Pi.one_apply]
    rw [if_neg (ne_of_lt hji), zero_add]
    split_ifs with h1
    · by_contra hu
      have := hsupp i hu
      subst h1
      rw [Fin.lt_def, Fin.val_rev] at hji
      omega
    · rfl
  · rw [fIwasawa_mk_val]
    simp only [pm, Matrix.of_apply, Pi.one_apply]
    rw [if_pos trivial]
    split_ifs with h1
    · have : u i = 0 := by
        by_contra hu
        have := hsupp i hu
        have h' := congrArg Fin.val h1
        rw [Fin.val_rev] at h'
        omega
      rw [this, add_zero]
    · rw [add_zero]
end GlobalTheory.TorusNormal
