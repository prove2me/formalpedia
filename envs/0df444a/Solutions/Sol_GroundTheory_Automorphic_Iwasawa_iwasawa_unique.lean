-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.iwasawa_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:21.908537+00:00
-- url     : https://prove2.me/submissions/404e3b70-5bda-40ab-9daf-f7127dcc5813

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_diagGL_mul_mul_diagGL_apply_self
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_diagGL_mul_mul_inv_mem_unipotent
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_borel_inf_integralGL_iff
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_torusPow_mem_borel
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_eq_zero_of_valuation_zpow_uniformizer_eq_one
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution {u u' k k' : GL (Fin n) F} {l l' : Fin n → ℤ}
    (hu : u ∈ unipotent F n) (hu' : u' ∈ unipotent F n)
    (hk : k ∈ integralGL F n) (hk' : k' ∈ integralGL F n)
    (h : u * torusPow F n l * k = u' * torusPow F n l' * k') :
    l = l' ∧ ∃ m ∈ unipotent F n ⊓ integralGL F n,
      u' = u * torusPow F n l * m * (torusPow F n l)⁻¹ := by
  have hπ : (GLnLocal.uniformizer F : F) ≠ 0 := (uniformizerUnit F).ne_zero
  have hx : (torusPow F n l')⁻¹ * (u'⁻¹ * u) * torusPow F n l = k' * k⁻¹ := by
    calc (torusPow F n l')⁻¹ * (u'⁻¹ * u) * torusPow F n l
        = (torusPow F n l')⁻¹ * u'⁻¹ * (u * torusPow F n l * k) * k⁻¹ := by group
      _ = (torusPow F n l')⁻¹ * u'⁻¹ * (u' * torusPow F n l' * k') * k⁻¹ := by rw [h]
      _ = k' * k⁻¹ := by group
  have hw : u'⁻¹ * u ∈ unipotent F n := (unipotent F n).mul_mem ((unipotent F n).inv_mem hu') hu
  have hxBK : (torusPow F n l')⁻¹ * (u'⁻¹ * u) * torusPow F n l ∈
      borel F n ⊓ integralGL F n := by
    refine ⟨?_, hx ▸ (integralGL F n).mul_mem hk' ((integralGL F n).inv_mem hk)⟩
    exact (borel F n).mul_mem ((borel F n).mul_mem ((borel F n).inv_mem
      (torusPow_mem_borel F n l')) hw.1) (torusPow_mem_borel F n l)
  have hll : l = l' := by
    funext i
    have hv := ((mem_borel_inf_integralGL_iff F n).1 hxBK).2.2 i
    rw [torusPow, torusPow, ← map_inv, diagGL_mul_mul_diagGL_apply_self F n hw] at hv
    have h0 : valuation F ((GLnLocal.uniformizer F : F) ^ (l i - l' i)) = 1 := by
      rw [← hv]
      congr 1
      rw [zpow_sub₀ hπ]
      simp [Units.val_zpow_eq_zpow_val, div_eq_mul_inv, mul_comm]
    have := eq_zero_of_valuation_zpow_uniformizer_eq_one F h0
    omega
  subst hll
  refine ⟨rfl, (torusPow F n l)⁻¹ * (u⁻¹ * u') * torusPow F n l, ⟨?_, ?_⟩, by group⟩
  · have := diagGL_mul_mul_inv_mem_unipotent F n
      ((unipotent F n).mul_mem ((unipotent F n).inv_mem hu) hu')
      (fun i => uniformizerUnit F ^ l i)⁻¹
    rw [map_inv, inv_inv] at this
    exact this
  · have : (torusPow F n l)⁻¹ * (u⁻¹ * u') * torusPow F n l =
        ((torusPow F n l)⁻¹ * (u'⁻¹ * u) * torusPow F n l)⁻¹ := by group
    rw [this, hx]
    exact (integralGL F n).inv_mem ((integralGL F n).mul_mem hk' ((integralGL F n).inv_mem hk))
end GroundTheory.Automorphic.Iwasawa
