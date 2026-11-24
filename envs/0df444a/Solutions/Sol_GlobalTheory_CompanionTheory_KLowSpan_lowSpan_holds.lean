-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KLowSpan.lowSpan_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:50.127878+00:00
-- url     : https://prove2.me/submissions/c314dbf2-96df-48e3-8ca8-2ab226224488

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kself_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kstab_kLowSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kLowSpan_le
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_cdom_of_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_eq_smul_of_top
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kstab_orthogonal
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil



set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KLowSpan
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.KLowSpan
theorem _root_.solution : CompanionTheory.D.DSIC.LowSpan := by
  intro n ε V _ _ E μ v S hF hU hv0 hv hfd hS hvS
  have hle : kLowSpan ε E v ≤ S := kLowSpan_le hS hvS
  refine ⟨kLowSpan ε E v, hle, kself_mem, kstab_kLowSpan hF hv, ?_,
    fun ν x hx hx0 hν => cdom_of_weight hF hU hv.1 hx hx0 hν,
    fun x hx hμ => eq_smul_of_top hF hU hv0 hv.1 hx hμ⟩
  intro L hL hst
  have : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le (hL.trans hle)
  have hst' := kstab_orthogonal hU hst
  have hdis : ∀ u ∈ L, u ∈ Lᗮ → u = 0 := fun u h1 h2 =>
    inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 h2 u h1)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.exists_add_mem_mem_orthogonal (K := L) v
  have hyw : IsWeight E μ y := by
    intro a
    refine sub_eq_zero.1 (hdis _ (L.sub_mem (hst a a rfl y hy) (L.smul_mem _ hy)) ?_)
    have h := hv.1 a
    rw [hyz, map_add, smul_add] at h
    have : E a a y - (μ a : ℂ) • y = (μ a : ℂ) • z - E a a z := by
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hz) (hst' a a rfl z hz)
  obtain ⟨c, hc⟩ := eq_smul_of_top hF hU hv0 hv.1 (hL hy) hyw
  by_cases h0 : c = 0
  · left
    rw [h0, zero_smul] at hc
    rw [hc, zero_add] at hyz
    have h1 : kLowSpan ε E v ≤ Lᗮ := kLowSpan_le hst' (hyz ▸ hz)
    exact (Submodule.eq_bot_iff _).2 fun u hu => hdis u hu (h1 (hL hu))
  · right
    refine le_antisymm hL (kLowSpan_le hst ?_)
    have : v = c⁻¹ • y := by rw [hc, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [this]
    exact L.smul_mem _ hy
end GlobalTheory.CompanionTheory.KLowSpan
