-- Prove2me | solution 1 for GlobalTheory.TorusNormal.pm_supp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:36:10.504809+00:00
-- url     : https://prove2.me/submissions/4bf8254d-e2ed-42e6-b9d0-6a7d59aa2dfe

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.TorusNormal
open Formalism.UG.P
variable {L : Type} [Field L]
namespace GlobalTheory.TorusNormal
theorem _root_.solution {n : ℕ} (u : Fin n → L) (hsupp : ∀ i, u i ≠ 0 → 2 * i.val + 1 < n) (i : Fin n) :
    u (Fin.rev i) * u i = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have a := hsupp _ h1
  have b := hsupp _ h2
  rw [Fin.val_rev] at a
  omega
end GlobalTheory.TorusNormal
