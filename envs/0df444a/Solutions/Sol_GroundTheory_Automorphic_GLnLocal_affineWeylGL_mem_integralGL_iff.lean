-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.affineWeylGL_mem_integralGL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:27.496193+00:00
-- url     : https://prove2.me/submissions/98ff894a-abb6-4859-84f9-5ef980980ff2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_valuation_uniformizer_pos
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_permAct_symm_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_affineWeylGL_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_affineWeylGL_inr
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_permGL_mem_integralGL
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
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (w : ExtendedAffineWeyl n) :
    affineWeylGL F n w ∈ integralGL F n ↔ w.left = 1 := by
  constructor
  · intro hw
    obtain ⟨h1, h2⟩ := (mem_integralGL_iff F n).mp hw
    have hle : ∀ i, valuation F ϖ ^ (w.left i).toAdd ≤ 1 := by
      intro i
      have := h1 i (w.right⁻¹ i)
      rw [affineWeylGL_apply, if_pos (by simp)] at this
      rwa [Valuation.mem_integer_iff, map_zpow₀] at this
    have hle' : ∀ i, valuation F ϖ ^ (-(w.left i).toAdd) ≤ 1 := by
      intro i
      have := h2 (w.right⁻¹ i) i
      rw [← map_inv, affineWeylGL_apply, if_pos (by simp)] at this
      rw [Valuation.mem_integer_iff, map_zpow₀] at this
      simpa [permAct_symm_apply] using this
    funext i
    have hq := valuation_uniformizer_pos F
    have h0 : valuation F ϖ ^ (w.left i).toAdd = valuation F ϖ ^ (0 : ℤ) := by
      rw [zpow_zero]
      refine le_antisymm (hle i) ?_
      have hmul : valuation F ϖ ^ (w.left i).toAdd * valuation F ϖ ^ (-(w.left i).toAdd) = 1 := by
        rw [← zpow_add₀ hq.ne', add_neg_cancel, zpow_zero]
      by_contra hlt
      push Not at hlt
      have : valuation F ϖ ^ (w.left i).toAdd * valuation F ϖ ^ (-(w.left i).toAdd) < 1 :=
        mul_lt_one_of_lt_of_le hlt (hle' i)
      rw [hmul] at this
      exact lt_irrefl _ this
    have := (zpow_right_strictAnti₀ hq (valuation_uniformizer_lt_one F)).injective h0
    exact Multiplicative.toAdd.injective this
  · intro hw
    have : w = SemidirectProduct.inr w.right := SemidirectProduct.ext hw rfl
    rw [this, affineWeylGL_inr]
    exact permGL_mem_integralGL F n _
end GroundTheory.Automorphic.GLnLocal
