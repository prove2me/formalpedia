-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.G_eq_of_lattice_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:53.278947+00:00
-- url     : https://prove2.me/submissions/40b79b36-1968-4399-baf9-7631d6b19b0e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantHomothety
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
theorem _root_.solution {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice) (n : ℕ) :
    L'.G n = (c ^ n)⁻¹ * L.G n := by
  have hmem : ∀ l ∈ L.lattice, c * l ∈ L'.lattice := fun l hl ↦ by
    have : c * l ∈ (L'.lattice : Set ℂ) := by rw [h]; exact ⟨l, hl, rfl⟩
    exact this
  have hmem' : ∀ l ∈ L'.lattice, c⁻¹ * l ∈ L.lattice := fun l hl ↦ by
    have : l ∈ (c * ·) '' (L.lattice : Set ℂ) := by rw [← h]; exact hl
    obtain ⟨m, hm, rfl⟩ := this
    rwa [inv_mul_cancel_left₀ hc]
  let e : L.lattice ≃ L'.lattice :=
    { toFun := fun l ↦ ⟨c * l, hmem _ l.2⟩
      invFun := fun l ↦ ⟨c⁻¹ * l, hmem' _ l.2⟩
      left_inv := fun l ↦ by ext; simp [hc]
      right_inv := fun l ↦ by ext; simp [hc] }
  rw [PeriodPair.G, PeriodPair.G, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l ↦ ?_
  show ((c * (l : ℂ)) ^ n)⁻¹ = (c ^ n)⁻¹ * ((l : ℂ) ^ n)⁻¹
  rw [mul_pow, mul_inv]
end GroundTheory.Global.Elliptic
