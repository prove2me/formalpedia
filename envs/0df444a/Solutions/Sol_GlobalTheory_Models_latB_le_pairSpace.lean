-- Prove2me | solution 1 for GlobalTheory.Models.latB_le_pairSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:38.207018+00:00
-- url     : https://prove2.me/submissions/43450f08-fd78-4e21-b6f7-cb7a30b0aa6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
import Theorems.Thm_GlobalTheory_Models_mem_latB
import Theorems.Thm_GlobalTheory_Models_one_le_w_and_wst
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_PhiGam_sh_le_sh
import Theorems.Thm_GlobalTheory_PhiGam_sh_le_sh_of_le
import Theorems.Thm_GlobalTheory_PhiGam_sh_sh_eq
import Theorems.Thm_GlobalTheory_PhiGam_sh_zero_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
variable {k G : Type} [Field k] [Group G]
variable {l n : ℕ} {R : RingPG k l}
namespace GlobalTheory.Models
theorem _root_.solution {m r : ℕ} {D : ModPG R n (Vc k m)} {Dt : TopData n r} {N : Lats k n m}
    (h : ABC D Dt.w Dt.wst N) : latB D N ≤ pairSpace D Dt N := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := mem_latB.1 hp
  intro i
  obtain ⟨hw, hw'⟩ := one_le_w_and_wst Dt i
  have h0 : ∀ (a : ℤ) (P : Submodule k⟦X⟧ (Vc k m)), 0 ≤ a → P ≤ sh (-a) P := fun a P ha => by
    have := sh_le_sh_of_le (show -a ≤ 0 by omega) P
    rwa [sh_zero_eq] at this
  have hφ : D.φ i (x (i - 1)) ∈ pull (D.φ i) (N (i - 1)) := Submodule.subset_span ⟨_, hx _, rfl⟩
  rw [herrD_apply]
  refine ⟨?_, h.2.2 i _ (hx i), fun _ => Submodule.sub_mem _ ((h.2.1 i).1 hφ) (h0 _ _ (by omega) (hx i)),
    fun _ => ⟨Submodule.sub_mem _ (h0 _ _ (by omega) hφ) ?_, x i, hx i, by simp⟩⟩
  · simp only [map_sub, D.comm]
    abel
  · have := sh_le_sh (-Dt.wst i) (h.2.1 i).2
    rw [sh_sh_eq, neg_add_cancel, sh_zero_eq] at this
    exact this (hx i)
end GlobalTheory.Models
