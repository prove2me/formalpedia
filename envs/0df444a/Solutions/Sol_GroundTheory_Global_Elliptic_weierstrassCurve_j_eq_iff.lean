-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassCurve_j_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:40.203132+00:00
-- url     : https://prove2.me/submissions/c4c4c15a-06eb-40f6-b661-938125e8cb2a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantHomothety
import Theorems.Thm_GroundTheory_Global_Elliptic_G_eq_of_lattice_eq_smul
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_weierstrassCurve_j_eq_of_g__g__d45f84b81f0e
import Theorems.Thm_GroundTheory_Global_Elliptic_lattice_eq_of_G_eq
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_g__g__of_variableChange_2adc7180d0a8
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_G_eq_of_g__g__73f0116ddc71


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {L L' : PeriodPair} :
    (weierstrassCurve L).j = (weierstrassCurve L').j ↔
      ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = (c * ·) '' L.lattice := by
  constructor
  · intro hj
    obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj
    obtain ⟨h₂, h₃⟩ := g₂_g₃_of_variableChange hC
    set t : ℂ := ((C.u⁻¹ : ℂˣ) : ℂ)
    have ht : t ≠ 0 := (C.u⁻¹).ne_zero
    have hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k) := fun k hk ↦
      G_eq_of_g₂_g₃ (L := L) h₂ h₃ hk
    exact ⟨t⁻¹, inv_ne_zero ht, lattice_eq_of_G_eq ht hG⟩
  · rintro ⟨c, hc, h⟩
    have hG := G_eq_of_lattice_eq_smul hc h
    refine weierstrassCurve_j_eq_of_g₂_g₃ (t := c⁻¹) (inv_ne_zero hc) ?_ ?_
    · rw [PeriodPair.g₂, PeriodPair.g₂, hG, inv_pow]
      ring
    · rw [PeriodPair.g₃, PeriodPair.g₃, hG, inv_pow]
      ring
end GroundTheory.Global.Elliptic
