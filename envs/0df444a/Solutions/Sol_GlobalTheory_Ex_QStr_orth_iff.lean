-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.orth_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:13.54259+00:00
-- url     : https://prove2.me/submissions/d386da32-7f5d-4fbb-a264-974f600d888e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Theorems.Thm_GlobalTheory_Ex_QStr_root_over
import Theorems.Thm_GlobalTheory_Ex_QStr_exists_nsmul
import Theorems.Thm_GlobalTheory_Ex_NumD_QT_pow_b
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_iff
import Theorems.Thm_GlobalTheory_Ex_NumD_wp_of_eq_zero
import Theorems.Thm_GlobalTheory_Ex_NumD_wp_swap
import Theorems.Thm_GlobalTheory_T_degenerationWeilPairing_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
variable {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ}
namespace GlobalTheory.Ex.QStr
theorem _root_.solution (hk : (k : C) ≠ 0)
    (nd : ∀ b : N.A, b ^ k = 1 → (∀ b', b' ^ k = 1 → N.weil k b b' = 1) → b = 1) (p : N.QT k) :
    (∀ p' : N.QT k, p'.1.1 = 1 → N.wp p p' = 1) ↔ ∃ p₀ : N.QT k, N.QEq p p₀ ∧ p₀.1.1 = 1 ∧ p₀.1.2.b = 1 := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  constructor
  · intro h
    obtain ⟨z, hz⟩ := exists_nsmul N hk p.1.1.toAdd fun t ht => by
      have := h (N.qTor t ht) rfl
      rwa [N.wp_swap, N.wp_qTor, inv_eq_one] at this
    have hq : N.QEq p (p * N.qTriv k (-z)) := (N.qEq_iff _ _).2 ⟨_, rfl⟩
    have h1 : (p * N.qTriv k (-z)).1.1.toAdd = 0 := by
      change p.1.1.toAdd + k • (-z) = 0
      rw [hz, smul_neg, add_neg_cancel]
    refine ⟨_, hq, h1, nd _ ?_ fun b' hb' => ?_⟩
    · rw [N.QT_pow_b, h1, N.c_zero]
    · obtain ⟨γ, hγ, hγ'⟩ := root_over N hk0 1 b' hb'
      let p' : N.QT k := ⟨(1, γ), hγ'.trans N.io_zero.symm⟩
      have e := N.wp_of_eq_zero (p * N.qTriv k (-z)) p' h1 rfl
      rw [← (GlobalTheory.T.degenerationWeilPairing_properties C N k p _ p').2.2.2.2.1 hq, h p' rfl] at e
      rw [← hγ]
      exact e.symm
  · rintro ⟨p₀, hq, h1, h2⟩ p' hp'
    rw [(GlobalTheory.T.degenerationWeilPairing_properties C N k p p₀ p').2.2.2.2.1 hq, (GlobalTheory.T.degenerationWeilPairing_properties C N k p₀ p' p').2.2.2.2.2.1 h1 h2, hp']
    exact NumD.Gt.s_zero _
end GlobalTheory.Ex.QStr
