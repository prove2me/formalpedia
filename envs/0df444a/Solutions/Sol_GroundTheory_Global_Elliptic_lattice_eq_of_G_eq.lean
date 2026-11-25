-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.lattice_eq_of_G_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:59.576342+00:00
-- url     : https://prove2.me/submissions/459d92b2-ddc7-4ce5-92cf-136eb068a24c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantHomothety
import Theorems.Thm_GroundTheory_Global_Elliptic_mul_mem_lattice_of_G_eq
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_zero
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_latticeOfTau____29e4a99442e2
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_one
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_two
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_zero
attribute [local simp] P2M_GroundTheory_Global_Elliptic_latticeOfTau____29e4a99442e2
attribute [local simp] P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620



set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) :
    (L'.lattice : Set ℂ) = (t⁻¹ * ·) '' L.lattice := by
  have hG' : ∀ k, 2 ≤ k → L.G (2 * k) = t⁻¹ ^ (2 * k) * L'.G (2 * k) := fun k hk ↦ by
    rw [hG k hk, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ ht)]
  ext z
  constructor
  · intro hz
    exact ⟨t * z, mul_mem_lattice_of_G_eq ht hG hz, by simp [ht]⟩
  · rintro ⟨w, hw, rfl⟩
    exact mul_mem_lattice_of_G_eq (inv_ne_zero ht) hG' hw
end GroundTheory.Global.Elliptic
