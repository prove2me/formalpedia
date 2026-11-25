-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.eq_of_affineWeylGL_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:30.224864+00:00
-- url     : https://prove2.me/submissions/4097cdcf-d656-4c73-9c78-e41916639648

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_valuation_uniformizer_pos
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_valuation_le_of_mem_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_perm_eq_one_of_forall_le
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
theorem _root_.solution {w w' : ExtendedAffineWeyl n}
    (h : affineWeylGL F n w' ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n)) :
    w = w' := by
  have h' : affineWeylGL F n w ∈
      doubleCoset (affineWeylGL F n w') (iwahori F n) (iwahori F n) := by
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp h
    refine mem_doubleCoset.mpr ⟨x⁻¹, (iwahori F n).inv_mem hx, y⁻¹, (iwahori F n).inv_mem hy, ?_⟩
    rw [hxy]
    group
  have heq : ∀ c, valuation F ϖ ^ (w'.left (w'.right c)).toAdd =
      valuation F ϖ ^ (w.left (w.right c)).toAdd := fun c =>
    le_antisymm (valuation_le_of_mem_doubleCoset F n h c).1
      (valuation_le_of_mem_doubleCoset F n h' c).1
  have hle : ∀ c, w'.right c ≤ w.right c := by
    intro c
    by_contra hlt
    push Not at hlt
    exact ((valuation_le_of_mem_doubleCoset F n h c).2 hlt).ne (heq c)
  have hπ := perm_eq_one_of_forall_le (w'.right * w.right⁻¹) (fun x => by
    simpa using hle (w.right⁻¹ x))
  have hright : w.right = w'.right := by
    have := congrArg (· * w.right) hπ
    simpa using this.symm
  have hinj := (zpow_right_strictAnti₀ (valuation_uniformizer_pos F)
    (valuation_uniformizer_lt_one F)).injective
  refine SemidirectProduct.ext ?_ hright
  funext i
  have := heq (w.right⁻¹ i)
  rw [← hright, show w.right (w.right⁻¹ i) = i from w.right.apply_symm_apply i] at this
  exact Multiplicative.toAdd.injective (hinj this).symm
end GroundTheory.Automorphic.GLnLocal
